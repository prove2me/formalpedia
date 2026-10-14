-- Prove2me | Theorems.Thm_Apery_energy_ineq
-- name    : Apery.energy_ineq
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T00:00:39.796973+00:00
-- url     : https://prove2.me/theorems/dba15bc7-c89f-4941-8349-eeab6af72887
-- title:
--   Equation (6.9) — the logarithmic-energy inequality for configurations
-- statement:
--   Let $n > 0$, $K = K_n = 40n$, $h = 37n$, and let $t_1,\dots,t_h > 0$ be pairwise distinct real numbers. With $V$ the field of (6.1), $\lambda = 37/40$, $M_0 = -1329/200$ and $I(\rho)$ the logarithmic energy of the comparison measure of Appendix A,
--
--   $$2\sum_{i<j}\log|t_i - t_j| \;-\; K\sum_{i=1}^{h} V(t_i) \;+\; \sum_{i=1}^{h}\sqrt{t_i} \;\le\; \bigl(\lambda M_0 - I(\rho)\bigr)K^2 \;+\; 5h \;+\; 6h\log K.$$
--
--   This is inequality (6.9) of the source, the configuration form of the logarithmic-energy inequality. It is obtained in the source (`Apery/EnergyFinal.lean`) from the raw energy inequality `energy_raw` with $\varepsilon = K^{-6}$ (`Apery/EnergyRaw.lean`), the potential inequality of Lemma 6.1 (`Table/Intervals.lean`, from the numerical certificates of Table 1), the tail bound (6.8) of Lemma 6.2 (`Table/Tail.lean`), and the bound on the regularisation error. It is the key input to the pointwise bound for the integrand of (6.10) in the proof of the energy bound (6.14) for $\log\Delta_n(\zeta(5))$.
--
--   **Formalization Note** The statement uses the platform definitions `Definitions.Def_Zeta5_SourceAnalytic` (for $V$), `Definitions.Def_Zeta5_SourceConstants` (for $K_n$) and `Definitions.Def_Zeta5_SourceMeasure` (for $\lambda, M_0, I(\rho)$); the configuration is indexed by `Fin (37 * n)`.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/EnergyBound.lean#L20-L25 (statement), proved in Apery/EnergyFinal.lean from Apery/EnergyRaw.lean, the certificates of Table 1 and the tail bound; inequality (6.9)

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceValue
import Definitions.Def_Zeta5_SourceConstants
import Definitions.Def_Zeta5_SourceMeasure
import Definitions.Def_Zeta5_SourceAnalytic

open Polynomial Filter Topology Finset

namespace Apery

theorem energy_ineq (n : ℕ) (hn : 0 < n) (t : Fin (37 * n) → ℝ) (ht : ∀ i, 0 < t i)
    (hinj : Function.Injective t) :
    (∑ i, ∑ j ∈ Finset.Ioi i, 2 * Real.log |t j - t i|) - Kr n * ∑ i, Vfield (t i) +
        ∑ i, Real.sqrt (t i) ≤
      (lam * M0 - Irho) * Kr n ^ 2 + 5 * (37 * n) + 6 * (37 * n) * Real.log (Kr n) := by sorry

end Apery
