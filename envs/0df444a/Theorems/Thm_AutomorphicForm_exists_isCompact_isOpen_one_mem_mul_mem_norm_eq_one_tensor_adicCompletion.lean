-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isCompact_isOpen_one_mem_mul_mem_norm_eq_one_tensor_adicCompletion
-- name    : AutomorphicForm.exists_isCompact_isOpen_one_mem_mul_mem_norm_eq_one_tensor_adicCompletion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/7cb08d85-00ac-50b9-83d0-71c564a71268
-- title:
--   A compact open subgroup of norm-one units in L⊗_K Kᵥ
-- statement:
--   Let $K$ and $L$ be number fields (each of type `Type`, with a fixed $K$-algebra structure on $L$), and let $v$ be a nonzero prime ideal of the ring of integers $\mathcal{O}_K$, i.e. a point of the height-one spectrum. Write $K_v$ for the $v$-adic completion of $K$ and consider the $K_v$-algebra $E = L \otimes_K K_v$. The assertion is that there exists a subset $G_0 \subseteq E$ with the following six properties: $G_0$ is compact; $G_0$ is open; the identity $1$ of $E$ lies in $G_0$; $G_0$ is closed under multiplication, that is $g h \in G_0$ for all $g, h \in G_0$; every $g \in G_0$ has a right inverse inside $G_0$, i.e. there is $h \in G_0$ with $gh = 1$ (so that in particular each element of $G_0$ is a unit of $E$); and for every $g \in G_0$ the absolute value of the $K_v$-algebra norm satisfies $\|N_{E/K_v}(g)\| = 1$. No further hypotheses on $v$, on the extension $L/K$, or on its ramification are imposed.
--
--   This is the local statement, at a finite place $v$ of $K$, that the semilocal unit group $\prod_{w \mid v} \mathcal{O}_w^{\times}$ is a compact open subgroup of $(L\otimes_K K_v)^{\times}$ on which the norm to $K_v$ has absolute value one; here it is packaged as a subset of $L \otimes_K K_v$ with the closure properties of a subgroup rather than as a bundled subgroup. It feeds the construction of compact open subgroups used in the measure-theoretic and convergence estimates for automorphic forms on $\mathrm{GL}_2$ over a number field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isCompact_isOpen_one_mem_mul_mem_norm_eq_one_tensor_adicCompletion.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal Pointwise
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.exists_isCompact_isOpen_one_mem_mul_mem_norm_eq_one_tensor_adicCompletion
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    ∃ G₀ : Set (L ⊗[K] v.adicCompletion K), IsCompact G₀ ∧ IsOpen G₀ ∧ (1 : L ⊗[K] v.adicCompletion K) ∈ G₀ ∧
      (∀ g ∈ G₀, ∀ h ∈ G₀, g * h ∈ G₀) ∧ (∀ g ∈ G₀, ∃ h ∈ G₀, g * h = 1) ∧
      (∀ g ∈ G₀, ‖Algebra.norm (v.adicCompletion K) g‖ = 1) := by sorry
