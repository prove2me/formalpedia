-- Prove2me | Theorems.Thm_AutomorphicForm_eq_zero_of_isCuspAutomorphicFnAt_productionPinsOf_of_coversModCentre_of_forall_mem_eq_zero
-- name    : AutomorphicForm.eq_zero_of_isCuspAutomorphicFnAt_productionPinsOf_of_coversModCentre_of_forall_mem_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/76b5d0b5-c36e-5608-8fd5-f5543f44fc97
-- title:
--   Cuspidal automorphic functions vanishing on a covering window vanish
-- statement:
--   Let $F$ be a number field, with ring of integers $\mathcal{O}_F$, and write $\mathrm{GL}_2(\mathbb{A}_F)$ for the general linear group of degree $2$ over the adele ring of $F$. Fix a subset $D \subseteq \mathrm{GL}_2(\mathbb{A}_F)$, a family $U$ of subgroups of $\mathrm{GL}_2(\mathbb{A}_F)$ indexed by the ideals of $\mathcal{O}_F$, a family $\mathrm{gen}$ of elements of $\mathrm{GL}_2(\mathbb{A}_F)$ indexed by the height-one primes of $\mathcal{O}_F$, and a subset $B$ of the adele ring; these assemble into the bundle of data `productionPinsOf F D U gen B`, whose measurable structures and measures are the Borel ones together with the Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$ and the conditioning of the additive Haar measure of $\mathbb{A}_F$ on $B$, and whose central slot $Z$ is the full group $\mathbb{A}_F^\times$ of idele units. Let $\xi \colon \mathbb{A}_F^\times \to \mathbb{C}^\times$ be a character of that slot and $\varphi \colon \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ a function satisfying `IsCuspAutomorphicFnAt` for these data, that is: $\varphi$ satisfies the predicate `LsXiMemberAt` relative to the Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$, the central slot with character $\xi$, and the set $D$; and $\varphi$ is cuspidal in the sense that its constant term along the unipotent family $x \mapsto \begin{pmatrix} 1 & x \\ 0 & 1\end{pmatrix}$, integrated against the conditioned measure on $B$, vanishes at every $g$. Let $W \subseteq \mathrm{GL}_2(\mathbb{A}_F)$ cover modulo the centre, i.e. for every $g \in \mathrm{GL}_2(\mathbb{A}_F)$ there are $\gamma \in \mathrm{GL}_2(F)$ and $z \in \mathbb{A}_F^\times$ with $\gamma g \cdot z I \in W$, where $\gamma$ and $z$ act through the adelic embedding and the central scalar embedding respectively. If $\varphi$ vanishes at every point of $W$, then $\varphi = 0$.
--
--   This is the consumer-facing form, for cuspidal automorphic functions attached to the production bundle of data, of the statement that an automorphic function with central character is determined by its restriction to a set covering $\mathrm{GL}_2(\mathbb{A}_F)$ modulo $\mathrm{GL}_2(F)$ on the left and the adelic centre on the right. It feeds the finite-dimensionality argument [`AutomorphicForm.finiteDimensional_of_forall_mem_rightConv_eq_self`](thm.html#AutomorphicForm.finiteDimensional_of_forall_mem_rightConv_eq_self), where injectivity of restriction to a covering window converts global statements into statements about the window.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_eq_zero_of_isCuspAutomorphicFnAt_productionPinsOf_of_coversModCentre_of_forall_mem_eq_zero.lean

import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_AutomorphicForm_AutomorphicFnAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm AutomorphicForm.SiegelCovering

theorem AutomorphicForm.eq_zero_of_isCuspAutomorphicFnAt_productionPinsOf_of_coversModCentre_of_forall_mem_eq_zero
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F) (B : Set (AdeleRing (𝓞 F) F))
    (ξ : (productionPinsOf F D U gen B).Z →* ℂˣ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsCuspAutomorphicFnAt F (productionPinsOf F D U gen B) ξ φ)
    (W : Set (AdelicGL2 (𝓞 F) F)) (hcov : CoversModCentre F W)
    (h0 : ∀ x ∈ W, φ x = 0) : φ = 0 := by sorry
