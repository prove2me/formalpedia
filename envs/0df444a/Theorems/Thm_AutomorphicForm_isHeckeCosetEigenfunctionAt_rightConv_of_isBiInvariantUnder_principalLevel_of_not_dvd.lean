-- Prove2me | Theorems.Thm_AutomorphicForm_isHeckeCosetEigenfunctionAt_rightConv_of_isBiInvariantUnder_principalLevel_of_not_dvd
-- name    : AutomorphicForm.isHeckeCosetEigenfunctionAt_rightConv_of_isBiInvariantUnder_principalLevel_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/b40ad452-0a96-5ecc-a193-a534f999a677
-- title:
--   Right convolution preserves Hecke eigenfunctions at good places
-- statement:
--   Let $L$ be a number field, let $N_1$ and $N$ be ideals of $\mathcal O_L$, and let $w$ be a finite place of $L$ (a height one prime $\mathfrak p_w$ of $\mathcal O_L$) with $\mathfrak p_w \nmid N_1$ and $\mathfrak p_w \nmid N$. For an ideal $M$ write $U(M) = \mathtt{principalLevel}(M) \sqcap \mathtt{finiteAdelicGL2Subgroup}$, the intersection of $\mathrm{levelOne}(M)$ with its conjugate by the Weyl element $\begin{pmatrix}0&1\\1&0\end{pmatrix}$, intersected with the kernel of the archimedean component map $\mathrm{GL}_2(\mathbb A_L) \to \mathrm{GL}_2(L \otimes \mathbb R)$; and let $t_w = \mathtt{heckeGen}(w)$ be the image in $\mathrm{GL}_2(\mathbb A_L)$ of $\mathrm{diag}(\varpi_w, 1)$ for the chosen uniformiser at $w$. Let $\varphi : \mathrm{GL}_2(\mathbb A_L) \to \mathbb C$ be continuous with compact support and satisfy $\varphi(ug) = \varphi(g) = \varphi(gu)$ for all $u \in U(N)$ and all $g$, and let $v : \mathrm{GL}_2(\mathbb A_L) \to \mathbb C$ be continuous with $v(gu) = v(g)$ for all $g$ and all $u \in U(N_1)$. Assume $a \in \mathbb C$ and that $v$ is a Hecke coset eigenfunction at level $U(N_1)$ for $t_w$ with eigenvalue $a$: there is a family $(r_i)$ indexed by $\mathrm{Fin}(\mathbf N(\mathfrak p_w)+1)$ of elements of the double coset $U(N_1)\,t_w\,U(N_1)$ whose classes in $\mathrm{GL}_2(\mathbb A_L)/U(N_1)$ are distinct and exhaust that double coset, and $\sum_i v(g r_i) = a\,v(g)$ for all $g$. Then the right convolution $g \mapsto \int v(gx)\varphi(x)\,dx$, taken with respect to the Haar measure `adelicGLHaar` on $\mathrm{GL}_2(\mathbb A_L)$ for its Borel $\sigma$-algebra, is a Hecke coset eigenfunction at level $U(N)$ for $t_w$ with the same eigenvalue $a$: there is a system $(s_i)$, indexed by $\mathrm{Fin}(\mathbf N(\mathfrak p_w)+1)$, of representatives of the left cosets of $U(N)$ in $U(N)\,t_w\,U(N)$ such that $\sum_i (v * \varphi)(g s_i) = a\,(v * \varphi)(g)$ for all $g$.
--
--   This is the compatibility of the spherical Hecke operator at a place $w$ prime to the levels with right convolution by a compactly supported test function bi-invariant under a principal congruence level subgroup: the eigenvalue is unchanged while the level group passes from $U(N_1)$ to $U(N)$. It is used in the construction of isotypic cusp forms by convolution, in [`AutomorphicForm.isIsotypicCuspFormAt_rightConv_of_isBiInvariantUnder_principalLevel_of_isFundamentalDomain_slab`](thm.html#AutomorphicForm.isIsotypicCuspFormAt_rightConv_of_isBiInvariantUnder_principalLevel_of_isFundamentalDomain_slab).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isHeckeCosetEigenfunctionAt_rightConv_of_isBiInvariantUnder_principalLevel_of_not_dvd.lean

import Definitions.Def_AutomorphicForm_UnitFactorizableOfType
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel
open IsDedekindDomain AutomorphicForm

theorem AutomorphicForm.isHeckeCosetEigenfunctionAt_rightConv_of_isBiInvariantUnder_principalLevel_of_not_dvd
    (L : Type) [Field L] [NumberField L]
    (N₁ N : Ideal (𝓞 L)) (w : HeightOneSpectrum (𝓞 L))
    (hw₁ : ¬ w.asIdeal ∣ N₁) (hw : ¬ w.asIdeal ∣ N)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hbi : IsBiInvariantUnder L (principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) φ)
    (v : AdelicGL2 (𝓞 L) L → ℂ) (hv : Continuous v)
    (hvU : ∀ g : AdelicGL2 (𝓞 L) L, ∀ u ∈ principalLevel (𝓞 L) L N₁ ⊓ finiteAdelicGL2Subgroup L,
      v (g * u) = v g)
    (a : ℂ)
    (ha : SmoothCusp.IsHeckeCosetEigenfunctionAt L (principalLevel (𝓞 L) L N₁ ⊓ finiteAdelicGL2Subgroup L)
      (heckeGen (𝓞 L) L w) w v a) :
    SmoothCusp.IsHeckeCosetEigenfunctionAt L (principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L)
      (heckeGen (𝓞 L) L w) w (rightConv L v φ) a := by sorry
