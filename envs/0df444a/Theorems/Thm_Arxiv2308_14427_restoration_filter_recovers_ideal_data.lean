-- Prove2me | Theorems.Thm_Arxiv2308_14427_restoration_filter_recovers_ideal_data
-- name    : Arxiv2308_14427.restoration_filter_recovers_ideal_data
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-26T13:16:55.44205+00:00
-- url     : https://prove2.me/theorems/d14b7bf6-c405-5f84-8714-600f31f92618
-- title:
--   Eqs. (4)-(6): the restoration filter recovers the aberration-free data
-- statement:
--   Work in the locally linear space-invariant model of the imaging system, with all signals sampled on $\mathbb{Z}\times\mathbb{Z}$, complex-valued and finitely supported, and $\ast$ the discrete convolution. Let $S$ be the tissue scatterer distribution, $\mathrm{PSF}_{\mathrm{aberrated}}$ the phase-aberrated point spread function, $\mathrm{PSF}_{\mathrm{ideal}}$ the ideal aberration-free point spread function, and $K$ a restoration filter, so that
--
--   $$\mathrm{PSF}_{\mathrm{ideal}}=\mathrm{PSF}_{\mathrm{aberrated}}\ast K\qquad(1).$$
--
--   Let the observed baseband data be $R_{\mathrm{aberrated}}=S\ast\mathrm{PSF}_{\mathrm{aberrated}}$ (2), and let $R_{\mathrm{ideal}}=S\ast\mathrm{PSF}_{\mathrm{ideal}}$ (3). Then
--
--   $$R_{\mathrm{aberrated}}\ast K=(S\ast\mathrm{PSF}_{\mathrm{aberrated}})\ast K=S\ast\mathrm{PSF}_{\mathrm{ideal}}=R_{\mathrm{ideal}},$$
--
--   which are eqs. (4), (5) and (6). In particular, filtering the phase-aberrated data with $K$ gives back the aberration-free data.
--
--   This identity is the basis of the paper's correction method: a filter $K$ that reshapes the aberrated PSF into the ideal one corrects every image formed with that PSF.
--
--   **Formalization Note** The paper writes $S\ast\mathrm{PSF}_{\mathrm{aberrated}}\ast K$ in eq. (4) without brackets. It is read as $(S\ast\mathrm{PSF}_{\mathrm{aberrated}})\ast K$, the substitution of eq. (2), and eq. (5) is the step that uses associativity. The paper does not specify its convolution; the statement uses the discrete convolution of finitely supported signals on the 2-D sample grid. Eq. (1) is a hypothesis here, assumed to hold exactly. The paper computes $K$ from eq. (1) by least squares, so in practice eq. (1) holds only approximately; no approximate version is stated. The "locally" in "locally linear space-invariant" is not modelled: eqs. (2) and (3) are assumed as single convolution identities on the whole grid $\mathbb{Z}\times\mathbb{Z}$, with no window or region boundary, as the paper writes them. $R_{\mathrm{ideal}}$ is defined by eq. (3), so the last equality holds by definition.
-- source:
--   Shen, Lin, Li and Li, Phase Aberration Correction with Adaptive Coherence-Weighted Point Spread Function Restoration Filtering Technique, arXiv:2308.14427v1 (2023), claim c010; Section II (locally linear space-invariant model) and Section II.A, eqs. (1)-(6), eq. (1) on PDF p. 1, eqs. (2)-(6) on PDF p. 2

import Mathlib
import Definitions.Def_Arxiv2308_14427_Basic

namespace Arxiv2308_14427

theorem restoration_filter_recovers_ideal_data (S psfAb psfId K Rab : Signal)
    (hK : IsRestorationFilter psfAb psfId K) (hRab : Rab = conv S psfAb) :
    conv Rab K = conv (conv S psfAb) K ∧
    conv (conv S psfAb) K = conv S psfId ∧
    conv S psfId = idealData S psfId := by sorry

end Arxiv2308_14427
