-- Prove2me | Theorems.Thm_ChowFormsCH_lemma_4_7
-- name    : ChowFormsCH.lemma_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:59:58.418411+00:00
-- url     : https://prove2.me/theorems/3af54c3c-9bb2-411d-a00b-375ab36ce962
-- title:
--   Lemma 4.7 — the squarefree part of $\gcd(R_G,R_H)$ is the Chow form of a codimension-$k$ $V_k\subseteq V$ containing its codimension-$k$ components
-- statement:
--   Let $K$ be algebraically closed, $F_1,\dots,F_m\in K[x_0,\dots,x_n]$ forms of degrees $d_1\ge\dots\ge d_m$ with $m\ge 1$ and $d_1\ge 1$, and $V:=V(F_1,\dots,F_m)\subseteq\mathbb P^n$. Let $B$ be a finite nonempty subset of the coefficient subfield of $K$ with $0\notin B$, and $1\le k\le n$. Let $G_1,\dots,G_k$ and $H_1,\dots,H_k$ be random linear combinations of $\{x_j^{d_1-d_i}F_i\}_{i,j}$ with coefficients picked independently and uniformly from $B$, and
--   $$
--   R_G:=\mathrm{TT}_t\,\mathrm{Res}\big((1-t)G_1+tx_1^{d_1},\dots,(1-t)G_k+tx_k^{d_1},L_0,\dots,L_{n-k}\big),
--   $$
--   $R_H$ likewise with the $H_i$. Then with probability at least
--   $$
--   1-\frac{4\,n\,d_1^{\,n}}{|B|}
--   $$
--   there is a projective variety $V_k\subseteq V$, equidimensional of codimension $k$ and containing every irreducible component of $V$ of codimension $k$, such that $\gcd(R_G,R_H)\neq 0$ and the squarefree part of $\gcd(R_G,R_H)$ is a nonzero scalar multiple of the Chow form of $V_k$.
--
--   This is the step of Theorem 4.9 that produces the Chow forms of the varieties $V^\star_k\supseteq V_k$, which are later pruned to the equidimensional components.
--
--   **Formalization Note** The coefficient subfield is the set of elements algebraic over the prime field. The random coefficient of $x_j^{d_1-d_l}F_l$ in the $(i+1)$-st combination is `a (false, i, l, j)` for $G$ and `a (true, i, l, j)` for $H$. The paper's $V_k$ here is not the equidimensional component; in Lean it is the existential `W`. Gcds and squarefree parts are unique up to units, and the claim is made for every choice.
--
--   Differences from the source:
--   - encoding: forms over a field F, B ⊆ F∖{0} a subset of the coefficient field of F, varieties over F̄ → an algebraically closed field K (of Type), B inside its coefficient subfield (elements algebraic over the prime field); reason: an instance over F is an instance over K = F̄, and the coefficient subfield of F lies in that of F̄
--   - reading: probability at least 1 − 4nd^n/|B| with d undefined in the statement → d = d₁, the largest degree; reason: only d₁ appears in R_G and R_H; the proof of Theorem 4.9 sets d := d₁ = max_i d_i
--   - reading: forms of degrees d₁ ≥ ⋯ ≥ d_m, resultants with degrees d₁ → m ≥ 1 and d₁ ≥ 1; reason: d₁ must exist, and Definition 2.5 fixes positive degrees for the resultant
--   - encoding: B a subset (sampled uniformly) → B finite and nonempty; reason: uniform sampling from B presupposes a finite nonempty set
--   - reading: the squarefree part of gcd(R_G, R_H) is a nonzero scalar multiple of the Chow form for some V_k ⊆ V → ∃ projective variety W ⊆ V, equidimensional of codimension k (possibly empty), containing every codimension-k component of V, with gcd(R_G, R_H) ≠ 0 and IsChowForm W for every gcd and every squarefree part; reason: the conclusion presupposes a nonzero gcd; gcds and squarefree parts are unique up to units; the empty variety is equidimensional by the paper's convention
-- source:
--   Andrews, Garg, Oliveira, Schost, Some algebraic and geometric computations in CH via Chow forms, arXiv:2611.05289 (held version, sha256 75e796c6…), Lemma 4.7, p.32 (PDF p.34)

import Mathlib
import Definitions.Def_ChowFormsCH_comps
import Definitions.Def_ChowFormsCH_IsChowForm
import Definitions.Def_ChowFormsCH_IsUnivResultant
import Definitions.Def_ChowFormsCH_IsSqfPart

set_option autoImplicit false

namespace ChowFormsCH

/-- **Lemma 4.7** (Andrews–Garg–Oliveira–Schost, *Some algebraic and geometric computations in CH
via Chow forms*, arXiv:2611.05289, held version, sha256 75e796c6…, p.32). Let `F₁, …, F_m` be forms
of degrees `d₁ ≥ ⋯ ≥ d_m` in `x₀, …, xₙ`, `V := V(F₁, …, F_m)`, `B` a finite subset of the coefficient
subfield of `K` not containing `0`, and `1 ≤ k ≤ n`. Let `G₁, …, G_k` and `H₁, …, H_k` be random linear
combinations of `{x_j^{d₁−d_i} F_i}_{i,j}` with coefficients independent and uniform in `B`, and
`R_G := TT_t Res((1 − t)G₁ + t x₁^{d₁}, …, (1 − t)G_k + t x_k^{d₁}, L₀, …, L_{n−k})`, `R_H` likewise.
Then with probability at least `1 − 4nd^n/|B|` (`d = d₁`) the squarefree part of `gcd(R_G, R_H)` is a
nonzero scalar multiple of the Chow form of some `V_k ⊆ V` that is equidimensional of codimension
`k` and contains every component of `V` of codimension `k`.

**Formalization Note** `K` is algebraically closed (an instance over a field `F` is an instance over
`F̄`, and its coefficient subfield contains that of `F`). `Res` is any universal resultant for the
degrees `(d₁, …, d₁, 1, …, 1)`; `d₁ ≥ 1` (resultants need positive degrees) and `m ≥ 1`. The random
coefficient of `x_j^{d₁−d_l} F_l` in `G_{i+1}` is `a (false, i, l, j)`, in `H_{i+1}` it is
`a (true, i, l, j)`. The variety `V_k` (the paper's name; not the equidimensional component) is the
existential `W`, a projective variety. The event includes `gcd(R_G, R_H) ≠ 0`, which the conclusion
presupposes; gcds and squarefree parts are unique up to units, and the claim is made for every
choice. -/
theorem lemma_4_7 {K : Type} [Field K] [IsAlgClosed K] {n m : ℕ} (hm : 0 < m)
    (F : Fin m → MvPolynomial (Fin (n + 1)) K) (d : Fin m → ℕ)
    (hF : ∀ i, (F i).IsHomogeneous (d i)) (hanti : Antitone d) (hd1 : 1 ≤ d ⟨0, hm⟩)
    (B : Finset K) (hB : B.Nonempty) (hB0 : (0 : K) ∉ B)
    (hBc : ∀ b ∈ B, IsAlgebraic (⊥ : Subfield K) b)
    (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ n)
    (R : MvPolynomial (ResVar n (perturbedDegrees (n := n) fun _ : Fin k => d ⟨0, hm⟩)) ℤ)
    (hR : IsUnivResultant n (perturbedDegrees (n := n) fun _ : Fin k => d ⟨0, hm⟩) R) :
    (1 : ℝ) - 4 * (n : ℝ) * ((d ⟨0, hm⟩ : ℕ) : ℝ) ^ n / (B.card : ℝ) ≤
      unifProb B (fun a : Bool × Fin k × Fin m × Fin (n + 1) → K =>
        ∃ W : Set (ProjSpace n K), IsProjVariety W ∧ W ⊆ projZero (Set.range F) ∧
          IsProjEquidim W (n - k) ∧
          (∀ Z ∈ comps (projZero (Set.range F)),
            topologicalKrullDim Z = ((n - k + 1 : ℕ) : WithBot ℕ∞) → Z ⊆ W) ∧
          ((resultantOf R (perturbedForms hk
                (fun i => ∑ l : Fin m, ∑ j : Fin (n + 1),
                  a (false, i, l, j) • (MvPolynomial.X j ^ (d ⟨0, hm⟩ - d l) * F l))
                (fun _ => d ⟨0, hm⟩))).trailingCoeff ≠ 0 ∨
           (resultantOf R (perturbedForms hk
                (fun i => ∑ l : Fin m, ∑ j : Fin (n + 1),
                  a (true, i, l, j) • (MvPolynomial.X j ^ (d ⟨0, hm⟩ - d l) * F l))
                (fun _ => d ⟨0, hm⟩))).trailingCoeff ≠ 0) ∧
          ∀ g s : MvPolynomial (Fin (n - k + 1) × Fin (n + 1)) K,
            IsGcdOf
              (resultantOf R (perturbedForms hk
                (fun i => ∑ l : Fin m, ∑ j : Fin (n + 1),
                  a (false, i, l, j) • (MvPolynomial.X j ^ (d ⟨0, hm⟩ - d l) * F l))
                (fun _ => d ⟨0, hm⟩))).trailingCoeff
              (resultantOf R (perturbedForms hk
                (fun i => ∑ l : Fin m, ∑ j : Fin (n + 1),
                  a (true, i, l, j) • (MvPolynomial.X j ^ (d ⟨0, hm⟩ - d l) * F l))
                (fun _ => d ⟨0, hm⟩))).trailingCoeff g →
            IsSqfPart g s → IsChowForm W (n - k) s) := by sorry

end ChowFormsCH
