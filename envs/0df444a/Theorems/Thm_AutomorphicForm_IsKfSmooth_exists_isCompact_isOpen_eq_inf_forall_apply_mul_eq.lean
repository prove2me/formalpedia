-- Prove2me | Theorems.Thm_AutomorphicForm_IsKfSmooth_exists_isCompact_isOpen_eq_inf_forall_apply_mul_eq
-- name    : AutomorphicForm.IsKfSmooth.exists_isCompact_isOpen_eq_inf_forall_apply_mul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/59a070db-35f1-5f8f-8e82-1635246f52ae
-- title:
--   K_f-smooth functions are right-invariant under a compact subgroup
-- statement:
--   Let $F$ be a number field, written with its ring of integers $\mathcal{O}_F$, and let $\varphi : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be a function on the group `AdelicGL2 (𝓞 F) F` of invertible $2 \times 2$ matrices over the adele ring of $F$. Write $\mathrm{GL}_2(\mathbb{A}_F)_f$ for the subgroup `finiteAdelicGL2Subgroup F`, defined as the kernel of the homomorphism $\mathrm{GL}_2(\mathbb{A}_F) \to \mathrm{GL}_2(\mathbb{A}_{F,\infty})$ obtained by applying the archimedean projection of the adeles entrywise. Assume $\varphi$ is $K_f$-smooth, i.e. that $\varphi$, regarded as an element of the type `RightTranslationFn` of functions $\mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ with its right-translation action of $\mathrm{GL}_2(\mathbb{A}_F)_f$, has open stabiliser inside $\mathrm{GL}_2(\mathbb{A}_F)_f$. Then there exist subgroups $U$ and $O$ of $\mathrm{GL}_2(\mathbb{A}_F)$ such that the underlying set of $U$ is compact, the underlying set of $O$ is open, $U = O \sqcap \mathrm{GL}_2(\mathbb{A}_F)_f$, and $\varphi(gk) = \varphi(g)$ for every $g \in \mathrm{GL}_2(\mathbb{A}_F)$ and every $k \in U$. (The compactness and openness assertions appear as further existential witnesses rather than conjuncts.)
--
--   This is the standard extraction of a compact open level subgroup from a smooth vector for the locally profinite group $\mathrm{GL}_2(\mathbb{A}_F^f)$: a $K_f$-smooth function is right-invariant under a compact subgroup of the full adelic group cut out of an open subgroup by the finite-adelic part. It feeds the analysis of the cuspidal spectrum, being used in the description of cuspidal constituents of an irreducible cuspidal subrepresentation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_IsKfSmooth_exists_isCompact_isOpen_eq_inf_forall_apply_mul_eq.lean

import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm

theorem AutomorphicForm.IsKfSmooth.exists_isCompact_isOpen_eq_inf_forall_apply_mul_eq
    (F : Type) [Field F] [NumberField F] (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsKfSmooth F φ) :
    ∃ (U : Subgroup (AdelicGL2 (𝓞 F) F)) (_ : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
      (O : Subgroup (AdelicGL2 (𝓞 F) F)) (_ : IsOpen (O : Set (AdelicGL2 (𝓞 F) F))),
      U = O ⊓ finiteAdelicGL2Subgroup F ∧ ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, φ (g * k) = φ g := by sorry
