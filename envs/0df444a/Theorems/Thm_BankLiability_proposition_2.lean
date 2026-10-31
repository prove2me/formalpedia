-- Prove2me | Theorems.Thm_BankLiability_proposition_2
-- name    : BankLiability.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:50:24.133927+00:00
-- url     : https://prove2.me/theorems/32561d17-64ca-44d1-bab3-05f58cb7f4bb
-- title:
--   Proposition 2: the strategic liability structure is unique, sets $V_d=V_b$, and is given by (5)–(7)
-- statement:
--   Fix parameters in Table 1's ranges satisfying the regularity assumption (4), $g^*<\eta/(1+\lambda)$, and an asset value $V>0$. Let $\pi$ be the state price (5), and $D^*/V$, $B^*/V$, $s^*$, $g^*$ the closed forms (6) and (7). Then:
--
--   1. there is exactly one strategic liability structure $(D,C_B)$, i.e. exactly one feasible structure maximizing the total bank value $F$;
--   2. at the strategic structure the state price of the regulatory boundary is $(V_b/V)^\lambda=\pi$, and the endogenous default boundary coincides with the regulatory total capital boundary:
--   $$\frac{V_b}{V}=\frac{V_d}{V}=\pi^{1/\lambda};$$
--   3. the deposit and nondeposit debt ratios are
--   $$\frac{D}{V}=(1-\beta)\pi^{1/\lambda},\qquad \frac{B}{V}=\Big(\frac{\tau}{1-\tau}+\beta+(1-\beta)\frac{\eta}{r}\frac{\lambda}{1+\lambda}+\frac{1-\pi}{\lambda}\Big)\pi^{1/\lambda};$$
--   4. the credit spread and the assessment rate are
--   $$s=\frac{r\pi}{1-\pi},\qquad g=(1-\omega)\frac{\alpha-\beta}{1-\beta}\cdot\frac{r\pi}{1-\pi}.$$
--
--   This is the paper's complete characterization of the value-maximizing bank: it uses nondeposit debt to place its own default boundary exactly at the regulator's closure boundary, which leaves no capital above the regulatory minimum at default and so minimizes the protection of the deposit insurer.
--
--   Differences from the source:
--   - reading: the paper's model under a geometric Brownian motion, with the total bank value given in the Online Appendix (not held) → the closed-form state-price model, with F = D + B + E from (15)–(17) without restructuring; reason: the Online Appendix is not part of the source; the reconstruction matches the §2 description and its maximizer reproduces Table 2 and the closed forms (5)–(7) numerically
--   - reading: regularity assumption (4) "g < η/(1+λ)" with g the structure-dependent assessment rate → g* < η/(1+λ) with g* the closed form (7); reason: the paper calls (4) an assumption on the parameters; required at every feasible D it is unsatisfiable (g° → ∞ as D/V → 1 − β), and this is the weakest parameter reading
--   - reading: "a bank's strategic liability structure (D*/V, B*/V)" → exactly one maximizing pair (D, C_B) exists, and every maximizer satisfies (5)–(7); reason: the definite description presupposes existence and uniqueness; the coupon C_B is the choice variable and B is determined by it (p.4: the triplet (I, C_D, C_B) determines the liability structure)
--   - reading: the minimum requirement printed as "V ≥ V_l = D/(1−β)" (p.6) → V ≥ max{V_b, V_d}; reason: D/(1−β) is V_b, while V_l = max{V_b, V_d} by the definition at the end of §2.2 (p.6), so the printed equation holds only when V_b ≥ V_d, and the requirement is read with the definition
--   - encoding: liability structures with V ≥ V_l → feasible structures 0 ≤ D < (1 − β)V, C_B ≥ 0, V_d ≤ V; reason: D = (1 − β)V is excluded because (2) is undefined there
--   - encoding: credit spread s with C_B = (r + s)B (p.4) → s = C_B/B − r; reason: the same number when B > 0, which the goal's B/V clause implies at the strategic structure
--   - generalization: 0 ≤ ω < 1 (p.6 text) → 0 ≤ ω ≤ 1 (Table 1); reason: the Lean statement covers ω = 1 as well and specializes to the p.6 range
-- source:
--   Sundaresan–Wang, Strategic Bank Liability Structure Under Capital Requirements, Management Science (2023), doi:10.1287/mnsc.2022.4570, Articles in Advance, Proposition 2, eqs. (5)–(7), p.7, under the regularity assumption (4), p.7

import Mathlib
import Definitions.Def_BankLiability_Params
import Definitions.Def_BankLiability_lam
import Definitions.Def_BankLiability_Model
import Definitions.Def_BankLiability_ClosedForms

namespace BankLiability

/-- **Proposition 2: the strategic liability structure exists, is unique, sets V_d = V_b, and is
given in closed form by (5)–(7).**
Sundaresan–Wang, *Strategic Bank Liability Structure Under Capital Requirements*, Management
Science (2023), doi:10.1287/mnsc.2022.4570, Articles in Advance, Proposition 2, p.7: "A bank's
strategic liability structure sets the deposit and nondeposit debt ratios so that the endogenous
default boundary coincides with the regulatory total capital boundary: V*_b/V = V*_d/V = π^{1/λ},
where π is the state price of regulatory total capital boundary, and it is related to the
parameters by (5). The deposit and nondeposit debt ratios are related to the parameters by
D*/V = (1−β)π^{1/λ}, B*/V = (τ/(1−τ) + β + (1−β)(η/r)(λ/(1+λ)) + (1−π)/λ)π^{1/λ}. (6) The credit
spread and assessment rate are related to the parameters by s* = rπ/(1−π),
g* = (1−ω)(α−β)/(1−β) · rπ/(1−π). (7)"

For parameters in Table 1's ranges satisfying the regularity assumption (4) and every asset value
`V > 0`:
1. there is exactly one strategic liability structure `(D, C_B)` (a maximizer of the total bank
   value over the feasible structures);
2. every strategic `(D, C_B)` satisfies: the state price of V_b is π of (5); `V_b/V = π^{1/λ}`
   and `V_d/V = π^{1/λ}`; `D/V` and `B/V` are the ratios (6); the credit spread and the
   assessment rate are `s*` and `g*` of (7).

**Formalization Note.** The model is the closed-form state-price model of
`Definitions.Def_BankLiability_Model` (total bank value reconstructed from (15)–(17) with no
restructuring; the paper's own closed form is in its Online Appendix). Assumption (4) is read as
the parameter condition `g* < η/(1+λ)` (`Regularity`). ω ranges over Table 1's `[0, 1]`. -/
theorem proposition_2 (P : Params) (hreg : Regularity P) (V : ℝ) (hV : 0 < V) :
    (∃! z : ℝ × ℝ, IsStrategic P V z.1 z.2) ∧
    ∀ D CB : ℝ, IsStrategic P V D CB →
      statePriceAt P V (regBoundary P D) = statePrice P ∧
      regBoundary P D / V = statePrice P ^ (1 / lam P) ∧
      defaultBoundary P V D CB / V = statePrice P ^ (1 / lam P) ∧
      D / V = depositRatioStar P ∧
      debtValue P V D CB / V = debtRatioStar P ∧
      creditSpread P V D CB = spreadStar P ∧
      assessRate P V D = assessRateStar P := by sorry

end BankLiability
