-- Prove2me | Theorems.Thm_CopylessCRA_lemma_9
-- name    : CopylessCRA.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:47:25.141417+00:00
-- url     : https://prove2.me/theorems/641921d7-8808-48c9-9ab6-ac3b24f79b88
-- title:
--   Display (3) and Lemma 9, p.8 — $P|_L$ is an affine coordinate permutation; $E=B_Q$ is the projection onto $\operatorname{im}B_\eta$ along $\ker B_\eta$, a polynomial in $B_\eta$
-- statement:
--   Let $P$ be a copyless map with $k(P\circ P)=k(P)$ (in the paper $P=P_\eta$ with $\eta$ minimizing $k(P_\eta)$ in the monoid $\mathcal Y$), and $L=L_P$. Then:
--
--   1. (display (3)) there are a permutation $\pi$ of the free coordinates and $\alpha_i\in\mathbb Q^\times$, $\beta_i\in\mathbb Q$ with
--   $$A_i(t)=\alpha_i\,t_{\pi(i)}+\beta_i\qquad\text{for } A=P|_L,\ t\in L;$$
--   2. the copyless retraction $Q=A^{-1}\circ P$ (characterized by $P_i=\alpha_iQ_{\pi(i)}+\beta_i$ on free coordinates and $Q_i=P_i$ on constant ones) is copyless, maps $\mathbb Q^r$ onto $L$ and satisfies $Q|_L=\mathrm{id}_L$;
--   3. (Lemma 9) $E=B_Q$ is idempotent on $V_r$, $\operatorname{im}E=\operatorname{im}B_P$ and $\ker E=\ker B_P$ (so $E$ is the projection onto $\operatorname{im}B_\eta$ along $\ker B_\eta$), and $E=p(B_P)$ on $V_r$ for some $p\in\mathbb Q[T]$.
--
--   Differences from the source:
--   - generalization: $P=P_\eta$ with $\eta$ minimizing $k(P_\eta)$ over the monoid $\mathcal Y$ → any copyless $P$ with $k(P\circ P)=k(P)$; reason: minimality gives $k(P_{\eta\eta})=k(P_\eta)$ since $\eta\eta\in\mathcal Y$; the proof uses only this
--   - generalization: copyless maps given by syntactic copyless tuples (§2.1) → maps with multiaffine coordinates and pairwise disjoint variable supports (`IsCopylessMap`); reason: every syntactic copyless tuple is such a map (proved in `Solutions/verification/CopylessCRA_syntactic.lean`), so the statement specializes to the paper's
--   - encoding: $Q=A^{-1}\circ P$ → $Q$ characterized by the polynomial identities $P_i=\alpha_iQ_{\pi(i)}+\beta_i$ (free $i$), $Q_i=P_i$ (constant $i$); reason: these identities say $A\circ Q=P$ with $Q$ valued in $L$, which determines $Q=A^{-1}\circ P$
-- source:
--   Zeng–Cao–Dai–Wang–Ding, Copyless Cost Register Automata and Algebraic Groups, STOC 2027 submission (manuscript sha256 434d3094df2665371c402d5b5291b3c7f3a27a0d79384e4a8ec3ca3a46a92543), display (3) and Lemma 9, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_CopylessCRA_CCRA
import Definitions.Def_CopylessCRA_IsCopylessMap

namespace CopylessCRA

/-- **Display (3) and Lemma 9.** Let `P = P_η` with `k = k(P)` and `L = L_P`, where `ηη` has exactly
`k` nonconstant coordinates. Then `A = P|_L : L → L` is an affine coordinate permutation,
`A_i(t) = α_i t_{π(i)} + β_i` with `α_i ∈ ℚ×` and `π` a permutation (3); the copyless retraction
`Q = A⁻¹ ∘ P : ℚ^r → L` is onto `L` with `Q|_L = id_L`, so `E = B_Q` is idempotent; and (Lemma 9)
`E` is the projection onto `im B_η` along `ker B_η`, and `E = p(B_η)` for some `p ∈ ℚ[T]`.

Zeng–Cao–Dai–Wang–Ding, *Copyless Cost Register Automata and Algebraic Groups*, STOC 2027
submission (manuscript sha256 434d3094…), display (3) and Lemma 9, p.8 (PDF p.10).

**Formalization Note** The paper takes `η` minimizing `k(P_η)` in the monoid `𝒴`; the proof uses only
`k(P_η ∘ P_η) = k(P_η)`, which minimality gives (`ηη ∈ 𝒴`). The statement is made for every copyless
`P` with `k(P ∘ P) = k(P)` (a generalization). The free coordinates are the nonconstant
coordinates of `P`; `π` permutes them. `Q` is characterized by `P_i = α_i Q_{π(i)} + β_i` on free
`i` and `Q_i = P_i` on constant `i`, which is `Q = A⁻¹ ∘ P`. `B_Q`, `B_P` act on `V_r`. -/
theorem lemma_9 {r : ℕ} (P : Fin r → MvPolynomial (Fin r) ℚ) (hP : IsCopylessMap P)
    (hk : numFree (compMap P P) = numFree P) :
    ∃ (π : Equiv.Perm {i // IsFreeCoord P i}) (a b : Fin r → ℚ),
      (∀ i, IsFreeCoord P i → a i ≠ 0) ∧
      (∀ x ∈ coordSubspace P, ∀ i (hi : IsFreeCoord P i),
        MvPolynomial.eval x (P i) = a i * x (π ⟨i, hi⟩) + b i) ∧
      ∃ Q : Fin r → MvPolynomial (Fin r) ℚ, IsCopylessMap Q ∧
        (∀ i (hi : IsFreeCoord P i),
          P i = MvPolynomial.C (a i) * Q (π ⟨i, hi⟩) + MvPolynomial.C (b i)) ∧
        (∀ i, ¬ IsFreeCoord P i → Q i = P i) ∧
        Set.range (evalMap Q) = coordSubspace P ∧
        (∀ x ∈ coordSubspace P, evalMap Q x = x) ∧
        (∀ h ∈ multiaffine r, pullback Q (pullback Q h) = pullback Q h) ∧
        (multiaffine r).map (pullback Q) = (multiaffine r).map (pullback P) ∧
        (∀ h ∈ multiaffine r, (pullback Q h = 0 ↔ pullback P h = 0)) ∧
        ∃ p : Polynomial ℚ, ∀ h ∈ multiaffine r,
          pullback Q h = Polynomial.aeval (pullback P) p h := by sorry

end CopylessCRA
