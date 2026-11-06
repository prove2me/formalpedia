-- Prove2me | Theorems.Thm_ConstrSOSP_sosp2_frame_exclusion
-- name    : ConstrSOSP.sosp2_frame_exclusion
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:09:29.195064+00:00
-- url     : https://prove2.me/theorems/3411b6c3-a0b2-4157-bed6-c77338b353cb
-- title:
--   Every $(\eta,\sqrt\eta)$-SOSP2 of $F$ lies in $[\rho,1-\rho]^2$
-- statement:
--   Let $C$ be a well-formed Iter circuit with $N=6\cdot2^n+6\ge10^{40}$, $F$ the normalized function, $\rho=1/12$, $\epsilon=\epsilon_0^2/(c_0^2N^4)$, $\eta=\rho^4\epsilon$ and $\sqrt\eta=\rho^2\sqrt\epsilon$.
--
--   **Theorem.** Every $(\eta,\sqrt\eta)$-SOSP2 $z$ of $F$ on $[0,1]^2$ lies in $[\rho,1-\rho]^2$.
--
--   On the added frame a feasible unit displacement decreases $F$ too fast for the first-order SOSP2 condition; Lemma B.3 then turns the remaining candidates into interior SOSPs.
--
--   Differences from the source:
--   - encoding: ∇f, ∇²f of the C² function → Mathlib Fréchet derivatives (gradVec, hessMat); vector norms written out as Euclidean norms; reason: Lean convention; same values for C² functions
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), proof of the constrained consequences of Theorem 5.1, p.57

import Mathlib
import Definitions.Def_ConstrSOSP_Circuit_WF
import Definitions.Def_ConstrSOSP_gridN
import Definitions.Def_ConstrSOSP_Fnorm
import Definitions.Def_ConstrSOSP_epsF
import Definitions.Def_ConstrSOSP_sqrtEpsF
import Definitions.Def_ConstrSOSP_boxA
import Definitions.Def_ConstrSOSP_boxB
import Definitions.Def_ConstrSOSP_IsSOSP2
import Definitions.Def_ConstrSOSP_gradVec
import Definitions.Def_ConstrSOSP_hessMat

namespace ConstrSOSP

/-- **The frame contains no approximate SOSP2** (arXiv:2604.02285, 2 Nov 2026, proof of the
constrained consequences of Theorem 5.1, p.57: "For SOSP2, set η = ρ^4 ϵ. We first show that every
(η, √η)-SOSP2 lies in [ρ, 1 − ρ]^2.").

For every well-formed Iter circuit `C` with `N = 6·2ⁿ + 6 ≥ 10⁴⁰`, `ρ = 1/12`,
`ϵ = ϵ₀²/(c₀²N⁴)`, `η = ρ⁴ϵ` and `√η = ρ²√ϵ = ρ²ϵ₀/(c₀N²)`, every `(η, √η)`-SOSP2 `z` of
`F = Fnorm C` on `[0, 1]²` (Definition 4.7) lies in `[ρ, 1 − ρ]²`. -/
theorem sosp2_frame_exclusion (C : Circuit) (hC : C.WF) (hN : 10 ^ 40 ≤ gridN C.n)
    (z : Fin 2 → ℝ)
    (hz : IsSOSP2 boxA boxB ((1 / 12 : ℝ) ^ 4 * ((epsF (gridN C.n) : ℚ) : ℝ))
      ((1 / 12 : ℝ) ^ 2 * ((sqrtEpsF (gridN C.n) : ℚ) : ℝ)) z
      (gradVec (Fnorm C) z) (hessMat (Fnorm C) z)) :
    ∀ i, (1 / 12 : ℝ) ≤ z i ∧ z i ≤ 1 - 1 / 12 := by sorry

end ConstrSOSP
