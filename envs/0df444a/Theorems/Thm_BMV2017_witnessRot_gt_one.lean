-- Prove2me | Theorems.Thm_BMV2017_witnessRot_gt_one
-- name    : BMV2017.witnessRot_gt_one
-- status  : Open
-- author  : @Alien60
-- created : 2026-10-08T23:55:00.143088+00:00
-- url     : https://prove2.me/theorems/2218825f-b8ee-4840-8c2f-c574c6ec5386
-- title:
--   p. 4 — at $\Delta\phi_{LR}=-0.2$, $\Delta\phi_{RL}=0.7$ a readjusted witness exceeds 1
-- statement:
--   Let $\rho=|\psi\rangle\langle\psi|$ with $\psi=\psi_{\mathrm{End}}(-0.2,\,0.7)=\tfrac12\big(|00\rangle+e^{-0.2i}|01\rangle+e^{0.7i}|10\rangle+|11\rangle\big)$. There exist real $\theta_1,\theta_2$ such that, with each spin's operators readjusted by the local phase rotation $R(\theta)=\operatorname{diag}(1,e^{i\theta})$, $\sigma^{\theta}=R(\theta)^\dagger\sigma R(\theta)$,
--   $$\mathcal W_{\theta_1,\theta_2}(\rho)=\big|\operatorname{Tr}\rho(\sigma_x^{\theta_1}\otimes\sigma_z^{\theta_2})-\operatorname{Tr}\rho(\sigma_y^{\theta_1}\otimes\sigma_y^{\theta_2})\big|>1 .$$
--
--   **Formalization Note** With the unrotated operators of p. 3 the witness on this state is about $0.08$, not the stated $\sim1.16$; the maximum over local phase rotations is $1+\sin(0.25)\approx1.25$. This corrected form is what is formalized; the value $1.16$ is not.
-- source:
--   S. Bose et al., A Spin Entanglement Witness for Quantum Gravity, Phys. Rev. Lett. 119, 240401 (2017), https://arxiv.org/abs/1707.06050v1, p. 4: phases ΔφLR ~ −0.2, ΔφRL ~ 0.7 and 'W ~ 1.16'; p. 4, readjusting the witness spin operators to local phases; witness defined on p. 3

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_BMV2017_defs

open Matrix
open scoped Kronecker ComplexOrder

namespace BMV2017

theorem witnessRot_gt_one :
    ∃ θ₁ θ₂ : ℝ, 1 < witnessRot θ₁ θ₂ (pureDM (psiEnd (-1 / 5) (7 / 10))) := by sorry

end BMV2017
