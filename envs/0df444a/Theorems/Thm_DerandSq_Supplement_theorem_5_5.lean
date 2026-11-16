-- Prove2me | Theorems.Thm_DerandSq_Supplement_theorem_5_5
-- name    : DerandSq.Supplement.theorem_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:10:44.923422+00:00
-- url     : https://prove2.me/theorems/e08bac30-60b7-4ca9-8292-51140bb7115a
-- title:
--   Theorem 5.5 — $\|Q(B^N)|_{\perp 1}\| \ge \|Q(t)\|_{C^*_{\mathrm{red}}(\Gamma)} - o_N(1)$ always, for $Q$ with non-negative coefficients
-- statement:
--   Fix $r$ colours and degrees $d_1, \dots, d_r$, and let $Q \in \mathbb R^*_{\ge 0}\langle x_1, \dots, x_r\rangle$ be a non-commutative ∗-polynomial with non-negative real coefficients. Then there is a function $f(N) \to 0$ (depending only on $r$, $d$ and $Q$) such that for every $N \ge 2$, all $d_i$-regular graphs $G_{N;1}, \dots, G_{N;r}$ on $[N]$ and all permutation matrices $U_1, \dots, U_r$ (so with probability 1 when they are random),
--
--   $$
--   \bigl\|Q(B^N)\big|_{\perp \mathbf 1}\bigr\| \ge \|Q(t)\|_{C^*_{\mathrm{red}}(\Gamma)} - f(N),
--   $$
--
--   where $B_i^N = U_i A_i^N U_i^*$ (5.1), $X|_{\perp\mathbf 1} = (I - J)X(I - J)$ with $J = \mathbf 1\mathbf 1^{\top}/N$, and $t_i = \sum_{j=1}^{d_i}\lambda(m_{i,j})$ on $\ell^2(\Gamma_{\vec d, r})$.
--
--   No girth assumption is needed. With Proposition 5.1 and Theorem 3.3 this recovers the Cohen–Cohen–Maor–Peled lower bound for rotating walks with arbitrary rotations.
--
--   **Formalization Note** "With probability 1" over the finite uniform space is "for every choice of permutations". Coefficients are the entries of `DerandSq.NCPoly 1 (Fin r)`; the norms are operator norms.
--
--   Differences from the source:
--   - reading: o_N(1) with probability 1 → ∃ f : ℕ → ℝ with f → 0, depending only on r, d and Q, such that the bound holds for every N ≥ 2, every d_i-regular graphs and every permutations; reason: the stronger (uniform) reading; the proof's error D·exp(−Ω(√log N)) + Δ(N) depends only on Q and d
--   - reading: d_i = O(1); B^N and t "as defined in (4.10)" → fixed degrees d : Fin r → ℕ; B_i and t_i of (5.1) and §5; reason: Γ_{d,r} and t depend on d; (4.10) defines the objects of §4, and the theorem is about the §5 objects of (5.1)
--   - encoding: with probability 1 over the uniform U^N → for every σ : Fin r → Perm (Fin N); reason: on a finite uniform space every point has positive mass, so the two are equivalent
--   - encoding: Q ∈ ℝ*_{≥0}⟨x_1,…,x_r⟩, Q(B^N)|_{⊥1}, ‖Q(t)‖_{C*_red(Γ)} → Q : NCPoly 1 (Fin r) with every coefficient real and ≥ 0, evaluated by NCPoly.eval; perpCompress 1 N; operator norm on ℓ²(Γ); reason: same polynomials and same norms (one copy of ℂ^N resp. ℓ²(Γ))
-- source:
--   Alev–Rao, Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks, STOC 2027 submission (manuscript sha256 2549f907…376941e0), Theorem 5.5, p.26

import Mathlib
import Definitions.Def_DerandSq_NCPoly_eval
import Definitions.Def_DerandSq_perpCompress
import Definitions.Def_DerandSq_Supplement_conjAdjOp
import Definitions.Def_DerandSq_Supplement_colTree

namespace DerandSq.Supplement

/-- Theorem 5.5 of Alev–Rao, *Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks*, STOC 2027 submission manuscript (sha256 2549f907…376941e0), p.26. Fix `r` colours and degrees `d_1, …, d_r`, and let
`Q ∈ ℝ*_{≥0}⟨x_1, …, x_r⟩` be a non-commutative ∗-polynomial with non-negative real coefficients.
Then for every `N ≥ 2`, `‖Q(B^N)|_{⊥1}‖ ≥ ‖Q(t)‖_{C*_red(Γ)} − o_N(1)` with probability 1, where
`B_i = U_i A_i U_i^*` (5.1) for `d_i`-regular graphs `G_{N;i}` on `[N]` and i.i.d. uniform
permutation matrices `U_i`, and `t_i = ∑_j λ(m_{i,j})` on `ℓ²(Γ_{d,r})`.

**Formalization Note** "`d_i = O(1)`" is read as fixed degrees. `o_N(1)` is one function
`f(N) → 0` depending only on `r`, `d` and `Q`, valid for every `N ≥ 2`, every `d_i`-regular
graphs and every permutations (the proof's bound `D·exp(−Ω(√log N)) + Δ(N)` is uniform); "with
probability 1" over the uniform finite space is "for every `σ`". The printed "as defined in
(4.10)" is read as (5.1). `Q` is a `DerandSq.NCPoly 1 (Fin r)` (scalar coefficients `Q w 0 0`)
evaluated by `DerandSq.NCPoly.eval` on one copy of `ℂ^N` resp. `ℓ²(Γ)`; `Y|_{⊥1}` is
`DerandSq.perpCompress 1 N Y = (I − J) Y (I − J)`; the reduced norm is the operator norm. -/
theorem theorem_5_5 (r : ℕ) (d : Fin r → ℕ) (Q : DerandSq.NCPoly 1 (Fin r))
    (hQ : ∀ w, (Q w 0 0).im = 0 ∧ 0 ≤ (Q w 0 0).re) :
    ∃ f : ℕ → ℝ, Filter.Tendsto f Filter.atTop (nhds 0) ∧
      ∀ (N : ℕ), 2 ≤ N → ∀ (G : Fin r → SimpleGraph (Fin N)) [∀ i, DecidableRel (G i).Adj],
        (∀ i, (G i).IsRegularOfDegree (d i)) → ∀ σ : Fin r → Equiv.Perm (Fin N),
          ‖Q.eval (fun i => colTree d i)‖ - f N ≤
            ‖DerandSq.perpCompress 1 N (Q.eval (fun i => conjAdjOp (G i) (σ i)))‖ := by sorry

end DerandSq.Supplement
