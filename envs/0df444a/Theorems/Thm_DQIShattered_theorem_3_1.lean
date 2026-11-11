-- Prove2me | Theorems.Thm_DQIShattered_theorem_3_1
-- name    : DQIShattered.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:30:33.568018+00:00
-- url     : https://prove2.me/theorems/88e6c46c-d00e-4eee-8c53-d938ee0d5b12
-- title:
--   Theorem 3.1 — $\mathbb E_J\,d_{\mathrm{TV}}(\mathcal D_{\mathrm{actual}},\mathcal D_{\mathrm{target}})\le\sqrt\delta$
-- statement:
--   Fix $B\in\mathbb F_2^{M\times N}$ and $\beta>0$, and let $\gamma=\frac12-\frac12\operatorname{sech}\beta$ (3.10). Let $U$ be any unitary decoder that solves the $(B,\gamma,\delta)$-quantum decoding problem. Then, for $J$ uniform on $\{+1,-1\}^M$,
--
--   $$\mathbb E_J\Big[d_{\mathrm{TV}}\big(\mathcal D_{\mathrm{actual}}(B,J,\beta),\,\mathcal D_{\mathrm{target}}(B,J,\beta)\big)\Big]\le\sqrt\delta .$$
--
--   Here $\mathcal D_{\mathrm{actual}}$ is the output law of the DQI procedure run with $U$, and $\mathcal D_{\mathrm{target}}$ is the measurement law of $|\Phi_{\mathrm{target}}\rangle$.
--
--   This is the step that turns a decoder failure rate into a sampling error. It is adapted from [SMR+26, Theorem 4].
--
--   Differences from the source:
--   - reading: D_actual is the output of the procedure when U_dec replaces the idealized decoder Ũ_dec → U is used as compute–copy–uncompute Ũ = (I ⊗ U†)·CX_{E→A}·(I ⊗ U); reason: Ũ equals (3.13)'s Ũ_dec for a perfect decoder; the literal reading (apply U† directly) makes (3.17) false, since an estimate-dependent phase after U keeps the success probability and shifts v
--   - reading: a unitary that solves the (B, γ, δ)-quantum decoding problem → a unitary on estimate ⊗ received ⊗ work registers whose answer, read on the estimate register, is d with average probability ≥ 1 − δ over d ∈ C^⊥; reason: the coherent form of Definition 2.2; the work register is needed by any real decoder, and an empty work register is allowed
--   - encoding: J uniform on {±1}^M, E_J → average over v ∈ 𝔽₂^M with J = (−1)^v; reason: bijection; same instances
-- source:
--   Zhou, Shutty, Sellke, Jordan, Gibbs Sampling in the Shattered Phase by Decoded Quantum Interferometry, arXiv:2609.40345 (held version sha256 0c7f6fdf…), Theorem 3.1, p.12

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_TVDist
import Definitions.Def_DQIShattered_DQI

namespace DQIShattered

/-- Zhou, Shutty, Sellke, Jordan, *Gibbs Sampling in the Shattered Phase by Decoded Quantum Interferometry*,
arXiv:2609.40345, held version sha256 0c7f6fdf…, Theorem 3.1 (adapted from [SMR+26, Theorem 4]), p.12.

Fix `B ∈ 𝔽₂^{M×N}` and `β > 0`, with `γ = 1/2 − (1/2) sech β` (3.10). Let `U` be any unitary (on estimate,
received and work registers) that solves the `(B, γ, δ)`-quantum decoding problem. Then, for uniformly random
`J ∈ {+1, −1}^M`,
`E_J[d_TV(𝒟_actual(B, J, β), 𝒟_target(B, J, β))] ≤ √δ`.

**Formalization Note** `𝒟_actual` is the output law of the procedure (3.11)–(3.16) with `U` used through
compute–copy–uncompute (see `Dactual`); `d_TV = ½ℓ¹`; `J = (−1)^v` with `v` uniform on `𝔽₂^M`. -/
theorem theorem_3_1 {M N : ℕ} (B : Matrix (Fin M) (Fin N) (ZMod 2)) (β : ℝ) (hβ : 0 < β) (δ : ℝ)
    {W : Type} [Fintype W] [DecidableEq W] (U : Matrix (Reg M × Reg M × W) (Reg M × Reg M × W) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Reg M × Reg M × W) ℂ) (w₀ : W)
    (hsolve : SolvesDecoding B (gammaOf β) δ U w₀) :
    (∑ v : Fin M → ZMod 2, IsingLTL.BeliefProp.tvDist (Dactual B v β U w₀) (Dtarget B v β)) / 2 ^ M ≤
      Real.sqrt δ := by sorry

end DQIShattered
