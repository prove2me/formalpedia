-- Prove2me | Theorems.Thm_AlgoPFR_claim_5_2_heavy_self_sums
-- name    : AlgoPFR.claim_5_2_heavy_self_sums
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:41:55.984313+00:00
-- url     : https://prove2.me/theorems/63878faa-3ea0-4f4a-b37c-6fe83e2a0b85
-- title:
--   Claim 5.2 — heavy self-sums live in a subspace $W$ with $d[X;U_W]=O(1)$
-- statement:
--   Let $0<\varepsilon<1/2$ and suppose $d[X;X]\le C_0$. There is a constant $C_1$ depending only on $\varepsilon,C_0$, and a subspace $W_0\le\mathbb F_2^n$ with $d[X;U_{W_0}]\le C_1$, such that for the quotient map $\pi:\mathbb F_2^n\to\mathbb F_2^n/W_0$ there is a set $S\subseteq\mathbb F_2^n/W_0$ with $|S|\le C_1$ and $\Pr[\pi(X)\in S]\ge1-\varepsilon$. Further, let $W=\pi^{-1}(\mathrm{Span}(S+S))$ and $Z=X+X'$ for an independent copy $X'$ of $X$. Then $d[X;U_W]\le C_1$, and every $z\notin W$ satisfies
--   $$p_Z(z)\le2\varepsilon\|p_X\|_\infty.$$
--
--   This is why the span of heavy self-sums is a small subspace, which Algorithm 3 extracts.
--
--   Differences from the source:
--
--   - encoding: ε a fixed constant, d[X;X] = O(1), and the O(1)s of the conclusion → ∀ ε, C₀ ∃ C₁ before n and X; reason: the same dependence of the constants
-- source:
--   Arunachalam, Dutt, Grewal, Gupte, Marton's conjecture in polynomial time, arXiv:2609.20771 (sha256 60e45066…), Claim 5.2, p.42

import Mathlib
import Definitions.Def_AlgoPFR_rd

set_option autoImplicit false

open scoped ENNReal Pointwise

namespace AlgoPFR

/-- **Claim 5.2.** Arunachalam, Dutt, Grewal, Gupte, *Marton's conjecture in polynomial time*, arXiv:2609.20771 (sha256 60e45066…), p.42: let `0 < ε < 1/2` be a fixed constant and `d[X;X] = O(1)`. Then there is a
subspace `W₀` with `d[X;U_{W₀}] = O(1)` such that, for the quotient map `π`, there is a set
`S ⊆ F₂ⁿ/W₀` with `|S| = O(1)` and `Pr[π(X) ∈ S] ≥ 1 − ε`. Further, for `W := π⁻¹(Span(S + S))` and
`Z := X + X′`: `d[X;U_W] = O(1)`, and every `z ∉ W` satisfies `p_Z(z) ≤ 2ε ‖p_X‖∞`.

**Formalization Note.** `d[X;X] = O(1)` is a bound `C₀`; the conclusion's `O(1)` is a constant `C₁`
depending only on `ε` and `C₀`, chosen before `n` and `X`. `‖p_X‖∞` is a supremum over the finite
nonempty type `Vec n`. -/
theorem claim_5_2_heavy_self_sums (ε C₀ : ℝ) (h0 : 0 < ε) (h1 : ε < 1 / 2) :
    ∃ C₁ : ℝ, ∀ (n : ℕ) (X : PMF (Vec n)), rd X X ≤ C₀ →
      ∃ (W₀ : Submodule (ZMod 2) (Vec n)) (S : Finset (Vec n ⧸ W₀)),
        rd X (subspaceLaw W₀) ≤ C₁ ∧ (S.card : ℝ) ≤ C₁ ∧
        ENNReal.ofReal (1 - ε) ≤ X.toOuterMeasure {x | W₀.mkQ x ∈ S} ∧
        rd X (subspaceLaw
          ((Submodule.span (ZMod 2) ((S : Set (Vec n ⧸ W₀)) + (S : Set (Vec n ⧸ W₀)))).comap
            W₀.mkQ)) ≤ C₁ ∧
        ∀ z, z ∉ (Submodule.span (ZMod 2) ((S : Set (Vec n ⧸ W₀)) + (S : Set (Vec n ⧸ W₀)))).comap
            W₀.mkQ →
          (sumLaw X X z).toReal ≤ 2 * ε * ⨆ x, (X x).toReal := by sorry

end AlgoPFR
