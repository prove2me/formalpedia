-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_isHeckeCosetEigenfunctionAt_finTranslateSum_of_levelOne_invariant
-- name    : AutomorphicForm.exists_forall_isHeckeCosetEigenfunctionAt_finTranslateSum_of_levelOne_invariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/5a3bbdb4-c96c-5502-96fc-5b89d806378a
-- title:
--   Hecke eigenvalues persist under translation to another level
-- statement:
--   Let $F$ be a number field, and let $N, N'$ be nonzero ideals of $\mathcal{O}_F$; write $U =$ `levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F` and $U'$ for the same group formed with $N'$, i.e. the level-$N$ (resp. level-$N'$) congruence subgroup of $\mathrm{GL}_2(\mathbb{A}_F)$ — the preimage under the projection to $\mathrm{GL}_2$ of the finite adeles of the subgroup of matrices which, together with their inverses, satisfy `IsLevelOneMatrix` for the ideal in question — intersected with the kernel of the projection $\mathrm{GL}_2(\mathbb{A}_F) \to \mathrm{GL}_2(\mathbb{A}_{F,\infty})$. For a finite place $v$ of $F$ let $g_v =$ `heckeGen (𝓞 F) F v` be the image of a uniformiser at $v$ under the map sending a unit of the completion $F_v$ to the adelic matrix $\mathrm{diag}(\cdot,1)$ supported at $v$. Given $a : v \mapsto a(v) \in \mathbb{C}$ and $\varphi' : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$, assume: $\varphi'(gk) = \varphi'(g)$ for all $g$ and all $k \in U'$; there is a finite set $S'$ of places such that for $v \notin S'$ one has `IsHeckeCosetEigenfunctionAt` for $(U', g_v, \varphi', a(v))$, that is, there exist $\mathbf{N}v + 1$ elements $r_0,\dots,r_{\mathbf{N}v}$ (where $\mathbf{N}v$ is the absolute norm of $v$) lying in the double coset $U' g_v U'$, whose cosets $r_i U'$ are pairwise distinct and exhaust the cosets $xU'$ with $x \in U' g_v U'$, and such that $\sum_i \varphi'(g r_i) = a(v)\varphi'(g)$ for all $g$; and there is a finite set $S_0$ such that for $v \notin S_0$ the double coset $U g_v U$ admits such a system of $\mathbf{N}v + 1$ representatives of left $U$-cosets. Let further $t$ be a finite set of elements of $\mathrm{GL}_2(\mathbb{A}_F)$ all lying in the kernel of the archimedean projection, $l$ a complex-valued weight function, and assume $\Psi = \sum_{h \in t} l(h)\,\varphi'(\cdot\, h)$ satisfies $\Psi(gk) = \Psi(g)$ for all $g$ and all $k \in U$. Then there is a finite set $S$ of places such that for every $v \notin S$ the function $\Psi$ satisfies `IsHeckeCosetEigenfunctionAt` for $(U, g_v, \Psi, a(v))$: the double-coset operator attached to $(U, g_v)$, computed with some system of $\mathbf{N}v + 1$ representatives of the left $U$-cosets in $U g_v U$, multiplies $\Psi$ by $a(v)$.
--
--   This is the level bookkeeping for the unramified Hecke operators: a right-$U$-invariant finite linear combination of finite-adelic right translates of an almost-everywhere Hecke eigenfunction of level $N'$ remains, outside a finite set of places, an eigenfunction with the same eigenvalues for the double-coset operators of level $N$. It is used in the construction of cuspidal realisations with prescribed archimedean weight from vectors in a translate span.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_isHeckeCosetEigenfunctionAt_finTranslateSum_of_levelOne_invariant.lean

import Definitions.Def_AutomorphicForm_SmoothCuspRealization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm AutomorphicForm.SmoothCusp HeckeIntegralSeam

theorem AutomorphicForm.exists_forall_isHeckeCosetEigenfunctionAt_finTranslateSum_of_levelOne_invariant
    (F : Type) [Field F] [NumberField F] (N N' : Ideal (𝓞 F)) (hN : N ≠ ⊥) (hN' : N' ≠ ⊥)
    (a : HeightOneSpectrum (𝓞 F) → ℂ) (φ' : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ'U : ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ levelOne (𝓞 F) F N' ⊓ finiteAdelicGL2Subgroup F,
      φ' (g * k) = φ' g)
    (S' : Finset (HeightOneSpectrum (𝓞 F)))
    (hφ' : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S' →
      IsHeckeCosetEigenfunctionAt F (levelOne (𝓞 F) F N' ⊓ finiteAdelicGL2Subgroup F)
        (heckeGen (𝓞 F) F v) v φ' (a v))
    (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
    (hsys : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S₀ →
      ∃ reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 F) F,
        IsHeckeCosetSystem (levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (heckeGen (𝓞 F) F v) reps)
    (t : Finset (AdelicGL2 (𝓞 F) F)) (l : AdelicGL2 (𝓞 F) F → ℂ)
    (ht : ∀ h ∈ t, h ∈ finiteAdelicGL2Subgroup F)
    (hU : ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F,
      ∑ h ∈ t, l h * φ' (g * k * h) = ∑ h ∈ t, l h * φ' (g * h)) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
      IsHeckeCosetEigenfunctionAt F (levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (heckeGen (𝓞 F) F v) v (fun g => ∑ h ∈ t, l h * φ' (g * h)) (a v) := by sorry
