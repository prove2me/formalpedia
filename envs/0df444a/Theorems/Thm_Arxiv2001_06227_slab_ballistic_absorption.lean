-- Prove2me | Theorems.Thm_Arxiv2001_06227_slab_ballistic_absorption
-- name    : Arxiv2001_06227.slab_ballistic_absorption
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T08:21:31.851069+00:00
-- url     : https://prove2.me/theorems/5701f0e6-e9e0-549b-961c-7304a916e90e
-- title:
--   Eq. (79): ballistic absorption of a slab, $\overline{P}_a=P_0[1-e^{-L/\ell_a}]$
-- statement:
--   Consider a slab of thickness $L>0$ and transverse section $S>0$, illuminated at normal incidence by a plane wave of specific intensity $\mathcal{I}_0>0$, with incident power $P_0=\mathcal{I}_0S$, energy velocity $v_E>0$ and extinction mean free path $\ell_e>0$, and assume $\ell_e=\ell_a$. Let the ballistic specific intensity $\mathcal{I}(s)$ at depth $s\ge0$ solve the RTE without its scattering source term, $\mathcal{I}'(s)=-\mathcal{I}(s)/\ell_e$, with $\mathcal{I}(0)=\mathcal{I}_0$. Then
--
--   $$\overline{P}_a=\frac{v_ES}{\ell_e}\int_0^L\frac{\mathcal{I}(s)}{v_E}\,ds=P_0\Big[1-\exp\Big(-\frac{L}{\ell_a}\Big)\Big],$$
--
--   $\overline{P}_a\le P_0$ for every $L>0$, and $\overline{P}_a\to P_0$ as $L\to\infty$: the maximum value $P_0$ is reached for $L\gg\ell_a$.
--
--   **Formalization Note** The RTE (44) without source, for a collimated beam at normal incidence, is written as the ordinary differential equation along the depth; the transverse integral over the section gives the factor $S$. The paper's approximation $\ell_e\simeq\ell_a$ is the hypothesis $\ell_e=\ell_a$. "Maximum for $L\gg\ell_a$" is formalized as the bound $\overline{P}_a\le P_0$ together with the limit $L\to\infty$. The remark on index mismatch is not included.
-- source:
--   Sheremet, Pierrat and Carminati, Absorption of scalar waves in correlated disordered media and its maximization using stealth hyperuniformity, arXiv:2001.06227v2 (2020), claim c027; Section IV.C, eqs. (78)-(79), PDF p. 8

import Mathlib
import Definitions.Def_Arxiv2001_06227_Basic

open MeasureTheory Filter Topology

namespace Arxiv2001_06227

theorem slab_ballistic_absorption (vE S I0 P0 ellE ellA : ℝ) (hvE : 0 < vE) (hS : 0 < S)
    (hI0 : 0 < I0) (hP0 : P0 = I0 * S) (hellE : 0 < ellE) (hea : ellE = ellA)
    (I : ℝ → ℝ) (hrte : ∀ s, 0 ≤ s → HasDerivWithinAt I (-(I s / ellE)) (Set.Ici 0) s)
    (hinit : I 0 = I0) :
    (∀ L, 0 < L → slabBallisticAbsorbed vE S ellE L I = P0 * (1 - Real.exp (-(L / ellA)))) ∧
    (∀ L, 0 < L → slabBallisticAbsorbed vE S ellE L I ≤ P0) ∧
    Tendsto (fun L => slabBallisticAbsorbed vE S ellE L I) atTop (𝓝 P0) := by sorry

end Arxiv2001_06227
