-- Prove2me | Theorems.Thm_ChoresEFX_perturbation_transfer
-- name    : ChoresEFX.perturbation_transfer
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:06:19.026886+00:00
-- url     : https://prove2.me/theorems/3ddf07f8-ef3f-415a-8930-1b39a4cdf1f7
-- title:
--   Proof of Theorem 1.1, pp.19–20 — perturbation transfer: $R^k_{i,\hat C}(B)=R^k_{i,C}(B)+\xi\max\{|B|-k,0\}$ and $\lambda_0$-EFkX for $\hat C$ gives $(2+1/k+\varepsilon)$-EFkX for $C$
-- statement:
--   Let $k\ge1$, $0<\varepsilon\le1$, let there be $m\ge1$ chores, $\xi=\varepsilon/(32m)$, let $C$ be a natural-number cost matrix, and $\hat C=C+\xi$. Then:
--
--   1. for every agent $i$ and bundle $B$, $R^k_{i,\hat C}(B)=R^k_{i,C}(B)+\xi\max\{|B|-k,0\}$;
--   2. every family of bundles that is $\lambda_0$-EFkX for $\hat C$, with $\lambda_0=2+1/k+\varepsilon/4$, is $(2+1/k+\varepsilon)$-EFkX for $C$;
--   3. for positive row scalars $D_i$, a family is $\alpha$-EFkX for $(D_ic_i)$ exactly when it is $\alpha$-EFkX for $c$.
--
--   This carries a guarantee for the working costs back to the original costs when some cost is zero.
--
--   Differences from the source:
--   - reading: unnumbered steps inside the proof of Theorem 1.1 and Corollary 1.2 → a stand-alone statement of the three facts; reason: they are the steps the proof asserts on pp.19–20
--   - generalization: a complete allocation; ε rational; D_i the row lcm → any family of bundles; ε real; any positive real D_i; reason: the argument uses nothing more, and the statement specializes to the proof's case
--   - generalization: n ≥ 2 agents (standing, §2, p.5) → any agent type (any n); reason: the argument does not use n ≥ 2, and the statement specializes to n ≥ 2
-- source:
--   Qin, Fang, Li, Liu, Chen, Polynomial-Time Approximate EFX for Chores via Flow and Matching, STOC 2027 submission (manuscript sha256 b26d14cf…), Proof of Theorem 1.1 and Corollary 1.2, pp.19–20

import Mathlib
import Definitions.Def_ChoresEFX_IsAlphaEFX

namespace ChoresEFX

/-- **The perturbation transfer**, proof of Theorem 1.1 and Corollary 1.2, pp.19–20.

Qin, Fang, Li, Liu, Chen, *Polynomial-Time Approximate EFX for Chores via Flow and Matching*, STOC 2027
submission (manuscript sha256 b26d14cf…).

With integer costs `C` and `Ĉ = C + ξ`, `ξ = ε/(32m)`: (a) for every bundle,
`R^k_{i,Ĉ}(B) = R^k_{i,C}(B) + ξ max{|B| − k, 0}`; (b) a `λ₀`-EFkX allocation for `Ĉ`, `λ₀ = 2 + 1/k + ε/4`, is
`(2 + 1/k + ε)`-EFkX for `C`; (c) row-wise scaling preserves all EFkX inequalities.

**Formalization Note.** Clause (b) needs the costs to be natural numbers: the step "`R` is a nonnegative integer
strictly below 1" uses it. `|κ| = m ≥ 1`. Clause (c) is stated for real scalars. -/
theorem perturbation_transfer {ι κ : Type*} [Fintype κ] [Nonempty κ] [DecidableEq κ]
    (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1) (Cn : ι → κ → ℕ) :
    (∀ (i : ι) (B : Finset κ),
      resid (fun i g => (Cn i g : ℝ) + ε / (32 * (Fintype.card κ : ℝ))) k i B =
        resid (fun i g => (Cn i g : ℝ)) k i B +
          ε / (32 * (Fintype.card κ : ℝ)) * max ((B.card : ℝ) - (k : ℝ)) 0) ∧
    (∀ X : ι → Finset κ,
      IsAlphaEFkX (fun i g => (Cn i g : ℝ) + ε / (32 * (Fintype.card κ : ℝ))) k
          (2 + 1 / (k : ℝ) + ε / 4) X →
        IsAlphaEFkX (fun i g => (Cn i g : ℝ)) k (2 + 1 / (k : ℝ) + ε) X) ∧
    (∀ (c : ι → κ → ℝ) (D : ι → ℝ) (α : ℝ) (X : ι → Finset κ), (∀ i, 0 < D i) →
      (IsAlphaEFkX (fun i g => D i * c i g) k α X ↔ IsAlphaEFkX c k α X)) := by sorry

end ChoresEFX
