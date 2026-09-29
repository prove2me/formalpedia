-- Prove2me | Theorems.Thm_DihedralWeightOne_exists_hasNebentypus_eq_weightOneLift_of_mem_span_of_apply_mul_finEmbed_eq_inv_mul
-- name    : DihedralWeightOne.exists_hasNebentypus_eq_weightOneLift_of_mem_span_of_apply_mul_finEmbed_eq_inv_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/302a1289-a696-560b-adc8-601d1531d55f
-- title:
--   Descent of adelic weight-one vectors to S₁(N,ε)
-- statement:
--   Fix a nonzero natural number $M$ and a cusp form $h$ of weight $1$ for $\Gamma_1(M)$, a nonzero natural number $N$ and a Dirichlet character $\varepsilon$ modulo $N$ with values in $\mathbb{C}$. Let $y$ be an element of the adelic span [`LocalNewvector.AdelicSpan`](def/LocalNewvector_AdelicSpanCarrier.html#L82) of the function $L =$ `weightOneLift (Ideal.span {(M : 𝓞 ℚ)}) h` on $\mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$; here $L(g)$ is, for $g$ admitting a decomposition $g = \gamma\, h'\, u$ with $\gamma \in \mathrm{GL}_2(\mathbb{Q})$, $u$ in the compact level subgroup at the ideal $(M)$, $h'$ with trivial finite part and with archimedean component in $\mathrm{GL}_2^+(\mathbb{R})$, the value $(h\mid_1 h'_\infty)(i)\cdot\det(h'_\infty)$, and $0$ otherwise. Assume (i) $y$ lies in the $\mathbb{C}$-span of the elements $\mathrm{finEmbed}(u)\cdot L$ for $u \in \mathrm{GL}_2$ of the finite adeles, where [`AdelicDock.finEmbed`](def/AdelicDock_LocalEmbedding.html#L145) is the embedding which is the identity matrix at the infinite places; and (ii) for every $u$ in the subgroup `finiteLevelZero` at the ideal $(N)$ (those $u$ with $u$ and $u^{-1}$ both satisfying `IsLevelZeroMatrix` at $(N)$) and every integer $d$ coprime to $N$ with $u_{11} - d$ in the level-$(N)$ ideal ball, one has $y(x\cdot \mathrm{finEmbed}(u)) = \varepsilon(d)^{-1} y(x)$ for all $x \in \mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$. Then there is a weight-one cusp form $F$ for $\Gamma_1(N)$ with nebentypus $\varepsilon$, i.e. $F(\gamma\tau) = \varepsilon(\gamma_{11})\,(\gamma_{10}\tau + \gamma_{11})\,F(\tau)$ for all $\gamma \in \Gamma_0(N)$ and $\tau$ in the upper half-plane, such that the function underlying $y$ equals `weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) F`, and such that $F = 0$ forces $y = 0$.
--
--   This is the descent, in weight one, from the adelic side to the space $S_1(N,\varepsilon)$: a vector in the span of right translates of the adelic lift of a weight-one form which transforms under the level-$(N)$ subgroup by $\varepsilon^{-1}$ is itself the adelic lift of a classical form of level $N$ and nebentypus $\varepsilon$. It is used in the analysis of newvectors at level $N$, notably by [`DihedralWeightOne.factorization_le_of_mem_span_weightOneLift_of_mem_fixedSubmodule_padicK1`](thm.html#DihedralWeightOne.factorization_le_of_mem_span_weightOneLift_of_mem_fixedSubmodule_padicK1).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DihedralWeightOne_exists_hasNebentypus_eq_weightOneLift_of_mem_span_of_apply_mul_finEmbed_eq_inv_mul.lean

import Mathlib
import Definitions.Def_AutomorphicForm_DihedralWeightOneLift
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_AdelicDock_LocalEmbedding

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm DihedralWeightOne IsDedekindDomain
open scoped MatrixGroups ModularForm

theorem DihedralWeightOne.exists_hasNebentypus_eq_weightOneLift_of_mem_span_of_apply_mul_finEmbed_eq_inv_mul
    {M : ℕ} [NeZero M] (h : CuspForm (CongruenceSubgroup.Gamma1 M) 1)
    {N : ℕ} [NeZero N] (ε : DirichletCharacter ℂ N)
    (y : LocalNewvector.AdelicSpan (weightOneLift (Ideal.span {(M : 𝓞 ℚ)}) (⇑h)))
    (hy : y ∈ Submodule.span ℂ (Set.range fun u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) =>
      (AdelicDock.finEmbed (𝓞 ℚ) ℚ u : AdelicGL2 (𝓞 ℚ) ℚ) •
        LocalNewvector.AdelicSpan.self (weightOneLift (Ideal.span {(M : 𝓞 ℚ)}) (⇑h))))
    (hK0 : ∀ u ∈ finiteLevelZero (𝓞 ℚ) ℚ (AdelicDock.ratLevel N), ∀ d : ℤ, IsCoprime d (N : ℤ) →
      (u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
          - algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (d : ℚ) ∈ idealBall (𝓞 ℚ) ℚ (AdelicDock.ratLevel N) →
      ∀ x : AdelicGL2 (𝓞 ℚ) ℚ,
        (LocalNewvector.AdelicSpan.toFn _ y).toFn (x * AdelicDock.finEmbed (𝓞 ℚ) ℚ u) =
          (ε (d : ZMod N))⁻¹ * (LocalNewvector.AdelicSpan.toFn _ y).toFn x) :
    ∃ F : CuspForm (CongruenceSubgroup.Gamma1 N) 1,
      CuspForm.HasNebentypus ε F ∧
      (LocalNewvector.AdelicSpan.toFn _ y).toFn = weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑F) ∧
      (F = 0 → y = 0) := by sorry
