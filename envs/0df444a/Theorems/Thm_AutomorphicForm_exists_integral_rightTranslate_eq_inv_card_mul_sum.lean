-- Prove2me | Theorems.Thm_AutomorphicForm_exists_integral_rightTranslate_eq_inv_card_mul_sum
-- name    : AutomorphicForm.exists_integral_rightTranslate_eq_inv_card_mul_sum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/21e87e00-488d-5a20-99f8-2af78de7230a
-- title:
--   Level average of a finite-adelic translate as Hecke coset sum
-- statement:
--   Let $F$ be a number field and let $G = \mathrm{GL}_2(\mathbb{A}_F)$ be the adelic general linear group `AdelicGL2 (𝓞 F) F`, i.e. the group of invertible $2\times 2$ matrices over the adele ring of $\mathcal{O}_F$ in $F$. Let $U \le G$ be a subgroup whose underlying set is compact, let $O \le G$ be a subgroup whose underlying set is open, and assume $U = O \cap \mathrm{ker}(\mathrm{glArch})$, where `finiteAdelicGL2Subgroup F` is the kernel of the homomorphism $G \to \mathrm{GL}_2(F \otimes \mathbb{R})$ induced entrywise by the projection of the adeles onto the infinite adeles. Let $\mu$ be a Haar probability measure on $U$ (with its Borel structure). Let $\varphi : G \to \mathbb{C}$ satisfy $\varphi(xu) = \varphi(x)$ for all $x \in G$, $u \in U$, and let $g$ lie in that same kernel. Then there exist $n \in \mathbb{N}$ and $\gamma : \mathrm{Fin}\,n \to G$ such that: each $\gamma_i$ is of the form $u g u'$ with $u, u' \in U$; every $x$ of the form $ugu'$ with $u,u' \in U$ satisfies $x = \gamma_i u''$ for some $i$ and some $u'' \in U$; $\gamma_i^{-1}\gamma_j \in U$ forces $i = j$; $n > 0$; and for every $x \in G$, $\int_U \varphi(x u g)\, d\mu(u) = n^{-1} \sum_{i} \varphi(x \gamma_i)$.
--
--   This identifies the average over the level group $U$ of the right translate of $\varphi$ by a finite-adelic element $g$ with the normalised Hecke double-coset operator $[UgU]$ applied to $\varphi$, the $\gamma_i$ being representatives of the right $U$-cosets in $UgU$. It is used in the analysis of cuspidal constituents, in the lemmas bounding intersections of cuspidal subrepresentations with invariant and archimedean-cut submodules, and in the dichotomy for principal cuspidal constituents.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_integral_rightTranslate_eq_inv_card_mul_sum.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField AutomorphicForm AutomorphicForm.CuspidalConstituent
open scoped BigOperators

theorem AutomorphicForm.exists_integral_rightTranslate_eq_inv_card_mul_sum
    (F : Type) [Field F] [NumberField F]
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    [MeasurableSpace U] [BorelSpace U] (μ : Measure U) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : ∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, φ (x * u) = φ x)
    {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ finiteAdelicGL2Subgroup F) :
    ∃ (n : ℕ) (reps : Fin n → AdelicGL2 (𝓞 F) F),
      (∀ i, ∃ u ∈ U, ∃ u' ∈ U, reps i = u * g * u') ∧
      (∀ x : AdelicGL2 (𝓞 F) F, (∃ u ∈ U, ∃ u' ∈ U, x = u * g * u') → ∃ i, ∃ u ∈ U, x = reps i * u) ∧
      (∀ i j, (reps i)⁻¹ * reps j ∈ U → i = j) ∧ 0 < n ∧
      ∀ x : AdelicGL2 (𝓞 F) F, ∫ u, φ (x * (u : AdelicGL2 (𝓞 F) F) * g) ∂μ = (n : ℂ)⁻¹ * ∑ i, φ (x * reps i) := by sorry
