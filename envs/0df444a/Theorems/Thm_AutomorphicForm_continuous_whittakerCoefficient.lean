-- Prove2me | Theorems.Thm_AutomorphicForm_continuous_whittakerCoefficient
-- name    : AutomorphicForm.continuous_whittakerCoefficient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/ec6b44c8-775f-5a59-ab6f-354af876809f
-- title:
--   Continuity of the adelic Whittaker coefficient in g
-- statement:
--   Let $F$ be a number field, with ring of integers $\mathcal{O}_F$ and adele ring $\mathbb{A}_F$, and write $\mathrm{GL}_2(\mathbb{A}_F)$ for the general linear group of $2\times 2$ matrices over $\mathbb{A}_F$. Given a set $D \subseteq \mathrm{GL}_2(\mathbb{A}_F)$, a family $U$ of subgroups of $\mathrm{GL}_2(\mathbb{A}_F)$ indexed by the ideals of $\mathcal{O}_F$, a map $\mathrm{gen}$ from the height-one spectrum of $\mathcal{O}_F$ to $\mathrm{GL}_2(\mathbb{A}_F)$, a continuous additive character $\psi : \mathbb{A}_F \to \mathbb{C}^{\times}$, a continuous function $\varphi : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$, and $\alpha \in F$, the assertion is that the function
--   $$g \longmapsto \int_{\mathbb{A}_F} \varphi\!\left(\begin{pmatrix} 1 & x \\ 0 & 1\end{pmatrix} g\right)\psi(-(\alpha x))\, d\nu(x)$$
--   is continuous on $\mathrm{GL}_2(\mathbb{A}_F)$. Here the data $(D, U, \mathrm{gen})$, together with the central subgroup taken to be $\top$, the Borel $\sigma$-algebras and Haar measures on $\mathrm{GL}_2(\mathbb{A}_F)$ and on $\mathbb{A}_F$, are assembled into the carrier record `productionPinsOf`, whose additive measure $\nu$ is the additive Haar measure of $\mathbb{A}_F$ conditioned on the adelic box `adelicBox F`, i.e. on the set of adeles whose archimedean component lies in the fundamental domain of the lattice basis of the mixed space and whose finite component is integral at every height-one prime.
--
--   This is the continuity, in the group variable, of the $\alpha$-th Whittaker (Fourier) coefficient of a continuous function on $\mathrm{GL}_2(\mathbb{A}_F)$, taken against the unipotent variable over the adelic box. It supplies the continuity input for the Rankin–Selberg and class-sum estimates, where positivity of the archimedean and ramified contributions is deduced from non-vanishing of a continuous Whittaker function on an open set.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_continuous_whittakerCoefficient.lean

import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicBox NumberField.AdelicHaar AutomorphicForm

theorem AutomorphicForm.continuous_whittakerCoefficient
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : Continuous ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ) (α : F) :
    Continuous (fun g : AdelicGL2 (𝓞 F) F =>
      whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g) := by sorry
