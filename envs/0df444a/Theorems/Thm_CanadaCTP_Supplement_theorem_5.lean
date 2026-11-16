-- Prove2me | Theorems.Thm_CanadaCTP_Supplement_theorem_5
-- name    : CanadaCTP.Supplement.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T17:38:14.412876+00:00
-- url     : https://prove2.me/theorems/ae76c519-0b57-40b2-b9be-1959670c8ad9
-- title:
--   Theorem 5 — expected cost $C(S,T)=1+\frac1{2\gamma}\big(\frac1{\gamma_T}+\frac{\gamma_T}{R^2}\big)$ of a simple policy
-- statement:
--   Consider an instance constructed as in Definition 10 and a simple policy with visiting order $\sigma$ and partition $(S,T)$ in which $S$ precedes $T$ and the safe path comes last. With $\gamma=\prod_{i\in[n]}u_i$ and $\gamma_T=\prod_{i\in T}u_i$, its expected cost is
--   $$C(S,T)=1+\frac1{2\gamma}\Big(\frac1{\gamma_T}+\frac{\gamma_T}{R^2}\Big).$$
--
--   The cost depends on the partition only through $\gamma_T$ and is minimized at $\gamma_T=R$, which links optimal policies to Subset Product in Theorem 6.
--
--   **Formalization Note** The expected cost is the published `CanadaCTP.expCost`, valued in $[0,\infty]$; the closed form is a positive real.
--
--   Differences from the source:
--   - encoding: paths 0 (safe) and 1, …, n; integers u_i, R → Fin (n+1), path 0 the safe path, path j.succ the paper's path j+1 for j : Fin n; u_i, R natural numbers; reason: Lean indexing; u_i ≥ 4 and R ≥ u_i − 1 ≥ 3 are positive, so the instances are the same
--   - encoding: a simple policy with visiting order σ and partition (S, T) (Definition 11) → Def10.simplePolicy σ S: deterministic, memory = position p in σ; at s it enters path σ p; at the middle vertex it traverses the second edge iff the path is safe, X_i = 0, or X_i = m_i and i ∉ S, else walks back to s (paying c_i) and moves to position p + 1; reason: Definition 11 fixes exactly the order, the m_i decisions, traversing 0 and never 3; a non-traversed path is left back to s and the next path of σ is entered, so the paper's simple policies are exactly these programs
--   - encoding: expected cost, a real number → expCost in ℝ≥0∞ equals ENNReal.ofReal of the closed form; reason: the published cost is valued in ℝ≥0∞; the closed form is positive
-- source:
--   Abels–Pitschmann–Schewior–Schmand, Canada Retravelled (manuscript, STOC 2027 submission, sha256 8117348eb78ba082edf376778214fa414f31cb0cd8a8d06c12a1dfba627e3a33), Theorem 5, p.25 (proof pp.25–26)

import Mathlib
import Definitions.Def_CanadaCTP_Supplement_Def10

namespace CanadaCTP.Supplement

open CanadaCTP

/-- Abels–Pitschmann–Schewior–Schmand, *Canada Retravelled* (manuscript, sha256 8117348e…3a33),
Theorem 5, p.25 (proof pp.25–26): for every instance of Definition 10 and every simple policy
`(σ, S)` whose visiting order `σ` has `S` before `T = [n] \ S` and the safe path last, the expected
cost is exactly
`C(S, T) = 1 + (1/(2γ))·(1/γ_T + γ_T/R²)`, with `γ = ∏_{i∈[n]} u_i`, `γ_T = ∏_{i∈T} u_i`.

**Formalization Note.** `expCost` is the published `CanadaCTP.expCost` (in `ℝ≥0∞`); the real
closed form is positive, so `ENNReal.ofReal` loses nothing. The value `δ = 1/(2R²)` is
substituted as in the theorem's last display. -/
theorem theorem_5 (D : Def10) (σ : Equiv.Perm (Fin (D.n + 1))) (S : Finset (Fin D.n))
    (hST : D.SPrecedesT σ S) (hsafe : D.SafeLast σ) :
    expCost D.inst (D.simplePolicy σ S) =
      ENNReal.ofReal (1 + 1 / (2 * D.gamma) * (1 / D.gammaT S + D.gammaT S / (D.R : ℝ) ^ 2)) := by sorry

end CanadaCTP.Supplement
