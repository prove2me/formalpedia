-- Prove2me | Theorems.Thm_FewInnerTSP_lemma_5_5
-- name    : FewInnerTSP.lemma_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:36:10.51153+00:00
-- url     : https://prove2.me/theorems/60d29caa-1da5-40f1-b713-bb3f18466874
-- title:
--   Lemma 5.5 (Per-step contraction)
-- statement:
--   Let $C>0$ be the constant of (13) (with its additive constant absorbed into $C\sqrt a$ on nonbase states), $\delta=16/17$, and as in (15)
--   $$L^*=\frac{2C}{1-\sqrt\delta},\qquad\gamma=\frac{2C}{1-\delta},\qquad\Psi(a,b)=L^*\sqrt a+b,\qquad\rho=\frac{C}{L^*+\gamma}.$$
--   Then $\rho>0$, and:
--
--   1. **The arithmetic step.** If $a\ge0$ and either $b\le\gamma\sqrt a$, $a_i\le\delta a$, $b_i\le b+C\sqrt a$, or $b>\gamma\sqrt a$, $a_i\le a$, $b_i\le\delta b+C\sqrt a$, then $\Psi(a_i,b_i)\le(1-\rho)\Psi(a,b)$.
--   2. **The calls of Algorithm 2.** Let $P$ be $n\ge3$ points in general position, $\Gamma$ a convex skeleton, $a_0>17$ with $\gamma\sqrt{a_0}\ge17$, and fix a valid separator rule. Let $S$ be a well-formed state with $a>a_0$ core vertices and $b$ terminals (a nonbase call), $Q$ its balancing set ($Q=A$ if $b\le\gamma\sqrt a$, $Q=B$ otherwise), and $\mathrm{Sel}$ a crossing candidate at the separator chosen for $(S,Q)$ with at most $C\sqrt a$ edges. Then each of the two child states, with $a_i$ core vertices and $b_i$ terminals, obeys
--   $$\Psi(a_i,b_i)\le(1-\rho)\,\Psi(a,b).$$
--
--   The potential $\Psi$ drops by a fixed fraction at every level, which bounds the recursion depth by $O(\log(k+2))$ and the accumulated core and terminal charge along every root-to-leaf path by $O(\sqrt k)$.
--
--   Differences from the source:
--   - reading: every child of every nonbase call obeys → clause 3: for every well-formed state with a > a₀ on a convex skeleton, its balancing set Q, a valid separator rule, every crossing candidate with at most C√a edges, and both child states; clause 2 adds the arithmetic step of the proof; reason: the cap |Sel| ≤ C√a is (13)'s, with its additive constant absorbed as p.11 says; Theorem 4.1 (ii) supplies it at the page's separator, while the Lean crossingChoices is defined for every valid rule, so the cap is a hypothesis
--   - generalization: the fixed C of (13) and the page's a₀, separator and candidate family → every C > 0, every a₀ > 17 with γ√a₀ ≥ 17, every valid separator rule, any convex skeleton; reason: the page's choices satisfy these hypotheses
--   - generalization: there is a constant ρ > 0 → the explicit ρ = C/(L∗ + γ), shown positive; reason: the page's proof names it ('Both cases allow ρ = C/(L∗+γ)')
-- source:
--   Li, Ma, Gong, Exact Euclidean TSP with Few Interior Points: A Square-Root Exponent, STOC 2027 submission (manuscript sha256 6541f631…), Lemma 5.5, p.12 (PDF p.14); (13), (15), §5.6, pp.10–11 (PDF pp.12–13)

import Mathlib
import Definitions.Def_FewInnerTSP_MixedRepr

namespace FewInnerTSP

/-- **Lemma 5.5 (Per-step contraction).** Li, Ma, Gong, *Exact Euclidean TSP with Few Interior Points: A
Square-Root Exponent*, STOC 2027 submission (manuscript sha256 6541f631…), Lemma 5.5, p.12 (PDF p.14),
with (13), (15) and §5.6, p.11 (PDF p.13): "There is a constant ρ > 0 such that every child of every
nonbase call obeys Ψ(ai, bi) ≤ (1 − ρ)Ψ(a, b)."

Fix the constant `C > 0` of (13) and `δ = 16/17`, and set as in (15)
`L∗ = 2C/(1 − √δ)`, `γ = 2C/(1 − δ)`, `Ψ(a, b) = L∗ √a + b`, and `ρ = C/(L∗ + γ)`. Then:
1. `ρ > 0`;
2. (the arithmetic of the proof) if `a ≥ 0` and either `b ≤ γ √a`, `aᵢ ≤ δ a`, `bᵢ ≤ b + C √a`, or
   `b > γ √a`, `aᵢ ≤ a`, `bᵢ ≤ δ b + C √a`, then `Ψ(aᵢ, bᵢ) ≤ (1 − ρ) Ψ(a, b)`;
3. (the calls of Algorithm 2) let `P` be `n ≥ 3` points in general position, `Γ` a convex skeleton, `a₀ > 17`
   with `γ √a₀ ≥ 17`, `sel` a valid separator rule, `S` a well-formed state with `a > a₀` (a nonbase call), `Q`
   its balancing set (`Q = A` if `b ≤ γ √a`, `Q = B` otherwise), and `Sel` a crossing candidate at `sel S Q`
   with at most `C √a` edges. Then each of the two child states, with parameters `(aᵢ, bᵢ)`, obeys
   `Ψ(aᵢ, bᵢ) ≤ (1 − ρ) Ψ(a, b)`.

**Formalization Note** The cap `|Sel| ≤ C √a` is (13)'s cap with its additive constant absorbed ("Absorb the
additive constant in equation (13) into C√a on all nonbase states", p.11): Theorem 4.1 (ii) supplies it at the
page's separator, while the Lean `crossingChoices` is the filter for every valid separator rule, so it is a
hypothesis here. The constant `ρ` is the one the proof names ("Both cases allow ρ = C/(L∗+γ)"). -/
theorem lemma_5_5 (C Lstar γ ρ : ℝ) (hC : 0 < C) (hL : Lstar = 2 * C / (1 - Real.sqrt (16 / 17)))
    (hγ : γ = 2 * C / (1 - 16 / 17)) (hρ : ρ = C / (Lstar + γ)) :
    0 < ρ ∧
    (∀ a b ai bi : ℝ, 0 ≤ a →
      ((b ≤ γ * Real.sqrt a ∧ ai ≤ 16 / 17 * a ∧ bi ≤ b + C * Real.sqrt a) ∨
        (γ * Real.sqrt a < b ∧ ai ≤ a ∧ bi ≤ 16 / 17 * b + C * Real.sqrt a)) →
      Lstar * Real.sqrt ai + bi ≤ (1 - ρ) * (Lstar * Real.sqrt a + b)) ∧
    (∀ (n m : ℕ), 3 ≤ n → ∀ P : Fin n → Pt, GeneralPos P → ∀ Γ : Skeleton n m, IsConvexSkeleton P Γ →
      ∀ a0 : ℕ, 17 < a0 → 17 ≤ γ * Real.sqrt (a0 : ℝ) →
      ∀ sel : Selector n m, IsValidSelector P Γ sel →
      ∀ S : State n m, IsState Γ S → a0 < S.A.card →
      ∀ Q : Finset (Fin n),
        (((S.B.card : ℝ) ≤ γ * Real.sqrt (S.A.card : ℝ) ∧ Q = S.A) ∨
          (γ * Real.sqrt (S.A.card : ℝ) < (S.B.card : ℝ) ∧ Q = S.B)) →
      ∀ Sel ∈ crossingChoices P Γ S (sel S Q), (Sel.card : ℝ) ≤ C * Real.sqrt (S.A.card : ℝ) →
      ∀ side : Bool,
        Lstar * Real.sqrt ((childState P Γ S (sel S Q) Sel side).A.card : ℝ) +
            ((childState P Γ S (sel S Q) Sel side).B.card : ℝ) ≤
          (1 - ρ) * (Lstar * Real.sqrt (S.A.card : ℝ) + (S.B.card : ℝ))) := by sorry

end FewInnerTSP
