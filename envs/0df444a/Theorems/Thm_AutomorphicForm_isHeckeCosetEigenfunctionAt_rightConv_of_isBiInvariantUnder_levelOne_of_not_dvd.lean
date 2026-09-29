-- Prove2me | Theorems.Thm_AutomorphicForm_isHeckeCosetEigenfunctionAt_rightConv_of_isBiInvariantUnder_levelOne_of_not_dvd
-- name    : AutomorphicForm.isHeckeCosetEigenfunctionAt_rightConv_of_isBiInvariantUnder_levelOne_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/74525d0e-89ce-52c7-ba89-bf6ad24a2652
-- title:
--   Right convolution preserves Hecke eigenvalues away from the levels
-- statement:
--   Let $L$ be a number field, let $N_1$ and $N$ be ideals of $\mathcal{O}_L$, and let $w$ be a finite place of $L$ (a height-one prime of $\mathcal{O}_L$) with $w \nmid N_1$ and $w \nmid N$. For an ideal $M$ write $U(M)$ for the subgroup `levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L` of $\mathrm{GL}_2$ of the adele ring of $L$, consisting of those $g$ whose archimedean component is trivial (i.e. $g$ lies in the kernel of `glArch`) and whose finite-adelic part, together with its inverse, satisfies the predicate `IsLevelOneMatrix` for $M$. Let $\varphi$ be a continuous, compactly supported function $\mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C}$ that is bi-invariant under $U(N)$, that is, $\varphi(ug) = \varphi(g) = \varphi(gu)$ for all $u \in U(N)$ and all $g$. Let $v$ be a continuous function $\mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C}$ with $v(gu) = v(g)$ for all $g$ and all $u \in U(N_1)$, and let $a \in \mathbb{C}$ be such that $v$ is a Hecke coset eigenfunction at $w$ with eigenvalue $a$ for $U(N_1)$ and the element $t_w =$ `heckeGen (𝓞 L) L w` (the image of the uniformiser unit at $w$ under `heckeGenAt`, concentrated at $w$): there is a family $(r_i)$ indexed by $\mathrm{Fin}(\mathrm{absNorm}(w)+1)$ which is a Hecke coset system for $U(N_1)$ and $t_w$ — each $r_i$ lies in the double coset $U(N_1) t_w U(N_1)$, every element of that double coset has the same image as some $r_i$ in $\mathrm{GL}_2(\mathbb{A}_L)/U(N_1)$, and $i \mapsto r_i U(N_1)$ is injective — and $\sum_i v(g r_i) = a\, v(g)$ for all $g$. Then the right convolution $(g \mapsto \int v(gx)\varphi(x)\,dx)$, the integral being against the Haar measure `adelicGLHaar` on $\mathrm{GL}_2(\mathbb{A}_L)$, is likewise a Hecke coset eigenfunction at $w$ with the same eigenvalue $a$, now for the group $U(N)$ and the same element $t_w$: there exists a Hecke coset system $(s_i)$ indexed by $\mathrm{Fin}(\mathrm{absNorm}(w)+1)$ for $U(N)$ and $t_w$ with $\sum_i (v * \varphi)(g s_i) = a\,(v * \varphi)(g)$ for all $g$.
--
--   This is the Hecke-equivariance half of the statement that right convolution by a test function bi-invariant under the level-$N$ subgroup carries eigenfunctions of level $N_1$ to eigenfunctions of level $N$ with the same eigenvalue at places prime to both levels, reflecting the commutativity of the spherical Hecke algebra of $(\mathrm{GL}_2(L_w), \mathrm{GL}_2(\mathcal{O}_w))$. It is used by [`AutomorphicForm.isIsotypicCuspFormAt_rightConv_of_isBiInvariantUnder_of_isFundamentalDomain_slab`](thm.html#AutomorphicForm.isIsotypicCuspFormAt_rightConv_of_isBiInvariantUnder_of_isFundamentalDomain_slab), where the convolution is shown to remain an isotypic cusp form.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isHeckeCosetEigenfunctionAt_rightConv_of_isBiInvariantUnder_levelOne_of_not_dvd.lean

import Definitions.Def_AutomorphicForm_UnitFactorizableOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel
open IsDedekindDomain AutomorphicForm

theorem AutomorphicForm.isHeckeCosetEigenfunctionAt_rightConv_of_isBiInvariantUnder_levelOne_of_not_dvd
    (L : Type) [Field L] [NumberField L]
    (N₁ N : Ideal (𝓞 L)) (w : HeightOneSpectrum (𝓞 L))
    (hw₁ : ¬ w.asIdeal ∣ N₁) (hw : ¬ w.asIdeal ∣ N)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hbi : IsBiInvariantUnder L (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) φ)
    (v : AdelicGL2 (𝓞 L) L → ℂ) (hv : Continuous v)
    (hvU : ∀ g : AdelicGL2 (𝓞 L) L, ∀ u ∈ levelOne (𝓞 L) L N₁ ⊓ finiteAdelicGL2Subgroup L,
      v (g * u) = v g)
    (a : ℂ)
    (ha : SmoothCusp.IsHeckeCosetEigenfunctionAt L (levelOne (𝓞 L) L N₁ ⊓ finiteAdelicGL2Subgroup L)
      (heckeGen (𝓞 L) L w) w v a) :
    SmoothCusp.IsHeckeCosetEigenfunctionAt L (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L)
      (heckeGen (𝓞 L) L w) w (rightConv L v φ) a := by sorry
