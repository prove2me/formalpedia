-- Prove2me | Theorems.Thm_AutomorphicForm_exists_sum_apply_mul_placeEmbed_repSome_add_apply_mul_placeEmbed_repInf_eq_of_isHeckeCosetEigenfunctionAt
-- name    : AutomorphicForm.exists_sum_apply_mul_placeEmbed_repSome_add_apply_mul_placeEmbed_repInf_eq_of_isHeckeCosetEigenfunctionAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/828dbb09-4f04-5998-bd88-5f8f1682f52a
-- title:
--   Explicit Hecke coset relation at v for any uniformiser
-- statement:
--   Let $F$ be a number field, $N$ an ideal of $\mathcal{O}_F$, and $v$ a nonzero prime of $\mathcal{O}_F$ with $v \nmid N$. Let $\varpi$ be an element of the valuation ring of the completion $F_v$ whose image in $F_v$ is nonzero and has valuation $\exp(-1)$, i.e. a uniformiser. Let $f : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ and $c \in \mathbb{C}$, and put $U = \mathtt{levelOne}\,N \sqcap \mathtt{finiteAdelicGL2Subgroup}$, the group of adelic matrices whose archimedean component is trivial and whose finite component, together with its inverse, satisfies the level-$N$ integrality condition `IsLevelOneMatrix`. Assume $f(gu) = f(g)$ for all $g$ and all $u \in U$, and assume `IsHeckeCosetEigenfunctionAt` holds for $U$, the Hecke generator `heckeGen (𝓞 F) F v` (the image in $\mathrm{GL}_2(\mathbb{A}_F)$ of $\mathrm{diag}(\cdot,1)$ at a distinguished uniformiser at $v$), $v$, $f$ and $c$: there is a family of $N(v)+1 = \mathrm{absNorm}(v)+1$ elements lying in the double coset $U\,g_v\,U$, hitting every coset $xU$ with $x$ in that double coset, with pairwise distinct cosets mod $U$, whose translates sum $f$ to $c\,f$. Then there exist $b_0,\dots,b_{N(v)-1}$ in the valuation ring of $F_v$ such that for every $g \in \mathrm{GL}_2(\mathbb{A}_F)$,
--   $$\sum_{i} f\Bigl(g\,\iota_v\begin{pmatrix}\varpi & b_i\\ 0 & 1\end{pmatrix}\Bigr) + f\Bigl(g\,\iota_v\begin{pmatrix}1 & 0\\ 0 & \varpi\end{pmatrix}\Bigr) = c\,f(g),$$
--   where $\iota_v$ is the place-$v$ embedding $\mathrm{GL}_2(F_v) \to \mathrm{GL}_2(\mathbb{A}_F)$ given by `localEmbed` followed by `finEmbed`.
--
--   This converts the abstract eigenfunction condition at an unramified place $v$ — eigenvalue $c$ for the sum over some system of left cosets in the double coset of the Hecke generator — into the classical explicit shape of the Hecke operator $T_v$ at level $N$, with representatives $\begin{pmatrix}\varpi & b\\ 0 & 1\end{pmatrix}$ over a residue system and $\begin{pmatrix}1&0\\0&\varpi\end{pmatrix}$, for an arbitrary uniformiser $\varpi$. It is used in the construction of the raw shaped vector, [`AutomorphicForm.shapedRaw_rawBundle_transl_rat`](thm.html#AutomorphicForm.shapedRaw_rawBundle_transl_rat), where the unramified Whittaker recursion requires the relation in this explicit form.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_sum_apply_mul_placeEmbed_repSome_add_apply_mul_placeEmbed_repInf_eq_of_isHeckeCosetEigenfunctionAt.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel AutomorphicForm UnramifiedWhittaker

theorem AutomorphicForm.exists_sum_apply_mul_placeEmbed_repSome_add_apply_mul_placeEmbed_repInf_eq_of_isHeckeCosetEigenfunctionAt
    (F : Type) [Field F] [NumberField F] (N : Ideal (𝓞 F)) (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ v.asIdeal ∣ N)
    (ϖ : v.adicCompletionIntegers F)
    (hπ : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) = WithZero.exp (-1 : ℤ))
    (f : AdelicGL2 (𝓞 F) F → ℂ) (c : ℂ)
    (hU : ∀ g : AdelicGL2 (𝓞 F) F, ∀ u ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F, f (g * u) = f g)
    (hf : SmoothCusp.IsHeckeCosetEigenfunctionAt F (levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (heckeGen (𝓞 F) F v) v f c) :
    ∃ b : Fin (Ideal.absNorm v.asIdeal) → v.adicCompletionIntegers F,
      ∀ g : AdelicGL2 (𝓞 F) F,
        (∑ i, f (g * placeEmbed F v (repSome (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) hπ
            (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (b i))))) +
          f (g * placeEmbed F v (repInf (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) hπ)) =
        c * f g := by sorry
