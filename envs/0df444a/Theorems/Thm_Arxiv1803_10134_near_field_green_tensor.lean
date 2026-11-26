-- Prove2me | Theorems.Thm_Arxiv1803_10134_near_field_green_tensor
-- name    : Arxiv1803_10134.near_field_green_tensor
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-26T13:09:50.408875+00:00
-- url     : https://prove2.me/theorems/20251b32-fdf2-564d-b845-b897da7ddf95
-- title:
--   Eq. (21): near-field form of the elastic Green's tensor
-- statement:
--   Let $\rho_0,c_p,c_s,\omega>0$. Then:
--
--   1. Separately, the compressive and the shear parts of eqs. (8) and (12) diverge as $1/\Delta r^3$. For every unit vector $\mathbf n$, as $t\to0^+$,
--   $$t^3\,\frac{e^{ik_pt}}{k_pt}\big[\mathbb 1-\hat F(k_pt\mathbf n)\big]\to3\Big(\frac{c_p}{\omega}\Big)^3(\mathbb 1-3\,\mathbf n\otimes\mathbf n),\qquad t^3\,\frac{e^{ik_st}}{k_st}\big[\mathbb 1+\tfrac12\hat F(k_st\mathbf n)\big]\to-\frac32\Big(\frac{c_s}{\omega}\Big)^3(\mathbb 1-3\,\mathbf n\otimes\mathbf n).$$
--   These $1/\Delta r^3$ terms cancel in $\hat{\mathcal G}=\frac{\omega}{12\pi\rho_0c_p^3}\{\cdots+2(c_p/c_s)^3\cdots\}$.
--   2. In the near field the Green's tensor reduces to eq. (21):
--   $$\Delta r\,\Big(\hat{\mathcal G}(\mathbf r,\mathbf r',\omega)-\frac{1}{8\pi\rho_0c_s^2\Delta r}\Big\{\Big[1+\Big(\frac{c_s}{c_p}\Big)^2\Big]\mathbb 1+\Big[1-\Big(\frac{c_s}{c_p}\Big)^2\Big]\frac{\Delta\mathbf r\otimes\Delta\mathbf r}{\Delta r^2}\Big\}\Big)\to0\qquad(\Delta\mathbf r\to0).$$
--   3. Every entry of the near-field tensor (21) is locally integrable on $\mathbb R^3$.
--
--   Since $\hat G_{mn}=B\hat{\mathcal G}(\mathbf r_m,\mathbf r_n,\omega)$ for $m\neq n$, item 2 gives $\hat G_{mn}\propto1/r_{mn}$ at small $r_{mn}$.
--
--   **Formalization Note** "In the near field $k_{p,s}\Delta r\ll1$, $\hat{\mathcal G}=$ (21)" is read as a leading-order statement: the difference is $o(1/\Delta r)$ as $\Delta\mathbf r\to0$ at fixed $\omega$. "Integrable in 3D" is read as local integrability, since (21) decays only like $1/\Delta r$ at infinity. The comparison with light is not part of the statement.
-- source:
--   Skipetrov and Beltukov, Anderson transition for elastic waves in three dimensions, arXiv:1803.10134v3 (2018), claim c018; Section III D, eq. (21) with eqs. (8) and (12), PDF p. 8

import Mathlib
import Definitions.Def_Arxiv1803_10134_Basic

open Complex MeasureTheory Filter Topology

namespace Arxiv1803_10134

theorem near_field_green_tensor (rho0 cp cs om : ℝ) (hrho0 : 0 < rho0) (hcp : 0 < cp)
    (hcs : 0 < cs) (hom : 0 < om) :
    (∀ n : Space, ‖n‖ = 1 →
      Tendsto (fun t : ℝ => ((t ^ 3 : ℝ) : ℂ) • compressivePart cp om (t • n)) (𝓝[>] 0)
        (𝓝 (((3 * (cp / om) ^ 3 : ℝ) : ℂ) • (1 - (3 : ℂ) • outerC n))) ∧
      Tendsto (fun t : ℝ => ((t ^ 3 : ℝ) : ℂ) • shearPart cs om (t • n)) (𝓝[>] 0)
        (𝓝 (((-(3 / 2) * (cs / om) ^ 3 : ℝ) : ℂ) • (1 - (3 : ℂ) • outerC n)))) ∧
    Tendsto (fun x : Space => ((‖x‖ : ℝ) : ℂ) •
        (greenTensor rho0 cp cs om x 0 - nearFieldTensor rho0 cp cs x 0)) (𝓝[≠] 0) (𝓝 0) ∧
    (∀ a b : Fin 3, LocallyIntegrable (fun x : Space => nearFieldTensor rho0 cp cs x 0 a b) volume) := by sorry

end Arxiv1803_10134
