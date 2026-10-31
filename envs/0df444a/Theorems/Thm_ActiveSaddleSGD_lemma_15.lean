-- Prove2me | Theorems.Thm_ActiveSaddleSGD_lemma_15
-- name    : ActiveSaddleSGD.lemma_15
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:11:53.570311+00:00
-- url     : https://prove2.me/theorems/a25c978a-8a2b-44e5-ac8a-da3544849f45
-- title:
--   Lemma 15 — $\mathbb P(U_n\to0)=0$
-- statement:
--   In the repulsive setting, for $c_H$, $c_r$, $c_{\tilde r,1}$, $c_{\tilde r,2}$ small enough,
--   $$
--   \mathbb P(U_n\to0)=0.
--   $$
--
--   Since $U_n$ is a norm of $w_n^-$, this excludes convergence of the iterates to the origin.
--
--   Differences from the source:
--   - encoding: "we can always choose $c_r$, $c_{\tilde r,2}$ and $L$" → $c_H$, $c_r$, $c_{\tilde r,1}$, $c_{\tilde r,2}$ existential, depending on $J^-$, $Q$ and the $C_\times$; reason: the setting is monotone in these constants, and $L$ is internal to the proof
-- source:
--   Bianchi, Hachem & Schechtman, Stochastic Subgradient Descent Escapes Active Strict Saddles on Weakly Convex Functions, arXiv:2108.02072v4, Lemma 15, p.34

import Mathlib
import Definitions.Def_ActiveSaddleSGD_ProjectedIterates
import Definitions.Def_ActiveSaddleSGD_CenterStable
import Definitions.Def_ActiveSaddleSGD_Repulsive

open MeasureTheory Filter Topology
open scoped ENNReal

namespace ActiveSaddleSGD

/-- Bianchi, Hachem & Schechtman, arXiv:2108.02072v4, Lemma 15, p.34: `ℙ(U_n → 0) = 0`.

**Formalization Note** The page chooses `c_r`, `c_{r̃,2}` small and `L` large; so `c_H`, `c_r`, `c_{r̃,1}`, `c_{r̃,2}` are
existential, depending on `J⁻`, `Q` and the `C_·` only. The setting is monotone in them, so one
choice serves all smaller ones. -/
theorem lemma_15.{v} {m : ℕ} (Jm Q : Matrix (Fin m) (Fin m) ℝ) (hm : 0 < m)
    (hJm : HasNegRealParts Jm) (hQ : Q.PosDef)
    (hL : Q * Jm + Jm.transpose * Q = -(2 : ℝ) • (1 : Matrix (Fin m) (Fin m) ℝ))
    (Ce1 Ce2 Crt : ℝ) (hCe1 : 0 < Ce1) (hCe2 : 0 < Ce2) (hCrt : 0 < Crt) :
    ∃ cH cr cr1 cr2 : ℝ, 0 < cH ∧ 0 < cr ∧ 0 < cr1 ∧ 0 < cr2 ∧
      ∀ (Ω : Type v) (mΩ : MeasurableSpace Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
        (ℱ : Filtration ℕ mΩ) (γ : ℕ → ℝ) (w : ℕ → Ω → EuclideanSpace ℝ (Fin m))
        (H : ℕ → Ω → Matrix (Fin m) (Fin m) ℝ)
        (e r rt : ℕ → Ω → EuclideanSpace ℝ (Fin m)),
        RepulsiveSetting μ ℱ γ Jm Q w H e r rt cH Ce1 Ce2 cr Crt cr1 cr2 →
        μ {ω | Tendsto (fun n => lyapNorm Q (w n) ω) atTop (𝓝 0)} = 0 := by sorry

end ActiveSaddleSGD
