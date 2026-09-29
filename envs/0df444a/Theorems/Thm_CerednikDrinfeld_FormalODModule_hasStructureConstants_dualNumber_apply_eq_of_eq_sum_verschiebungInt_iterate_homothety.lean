-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety
-- name    : CerednikDrinfeld.FormalODModule.hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/1fa183e0-f1aa-5752-b32d-21b9f2685192
-- title:
--   First-order structure constants of a reshaped V-basis over k[ε]
-- statement:
--   Let $q$ be a prime, $k$ a field of characteristic $q$, $j_0\colon W(\mathbb F_{q^2})\to k$ a ring homomorphism, and $X_0$ a formal $\mathcal O_D$-module over $k$, i.e. a two-dimensional commutative formal group law $X_0.F$ over $k$ together with an action of $W(\mathbb F_{q^2})$ and an endomorphism $\varpi$ satisfying the usual relations. Let $\gamma\colon \mathrm{Fin}\,2\to \mathrm{Cart}_q(X_0.F)$ be a homogeneous $V$-basis for $j_0$: each $\gamma_i$ lies in the $i$-th graded piece, meaning $[\,\omega(c)\,]$-equivariance $\gamma_i\circ\omega(c)=[\,j_0(\omega(c))^{q^i}\,]\gamma_i$ for all Teichmüller lifts $\omega(c)$, $c\in\mathbb F_{q^2}$, and the determinant of the tangent matrix $(\mathrm{tangent}(\gamma_i)_k)$ is a unit. Let $a\colon\mathbb N\to\mathrm{Fin}\,2\to k$ be structure constants for $\gamma$, i.e. for all $i$ and $N$ the element $\varpi\cdot\gamma_i$ equals $\sum_{m<N}V^m\bigl([a_{m,i}]\gamma_{i+m+1}\bigr)$ modulo $V^N\mathrm{Cart}_q(X_0.F)$, indices read modulo $2$ via `piIndex`. Let $\gamma'$ be a homogeneous $V$-basis, for $j_0$ followed by $k\to k[\varepsilon]$, of the Cartier module of the base change of $X_0$ along $k\to k[\varepsilon]$, and assume $s,v,w\colon\mathrm{Fin}\,2\to k$ and $g_i$ in that Cartier module satisfy, for every $i$, $$\gamma'_i=[1+s_i\varepsilon]\gamma_i^{\varepsilon}+V\bigl([v_i\varepsilon]\gamma^{\varepsilon}_{i+1}\bigr)+V^2\bigl([w_i\varepsilon]\gamma^{\varepsilon}_i\bigr)+V^3 g_i,$$ where $\gamma^\varepsilon$ denotes the base change of $\gamma$. Let $a'$ be structure constants for $\gamma'$. Then three assertions hold: for all $i$, $a'_{0,i}=a_{0,i}+(s_i-s_{i+1})a_{0,i}\,\varepsilon$; for all $i$, $a'_{1,i}=a_{1,i}+\bigl(v_i a_{0,i+1}-a_{0,i}^{\,q}v_{i+1}-a_{1,i}s_i\bigr)\varepsilon$; and for every index $i_0$ with $a_{0,i_0}=0$ such that $F\gamma_{i_0}$ lies in the image of $V$ on $\mathrm{Cart}_q(X_0.F)$, one has $a'_{2,i_0}=a_{2,i_0}-\bigl(a_{1,i_0}^{\,q}v_{i_0}+a_{2,i_0}s_{i_0+1}\bigr)\varepsilon$.
--
--   This is the first-order deformation calculus for Cartier structure constants of special formal $\mathcal O_D$-modules: it computes the structure constants of an arbitrary reshaped homogeneous $V$-basis of the trivial deformation of $X_0$ over the dual numbers, modulo $V^3$, in terms of those of $X_0$ and the reshaping data $s,v$. It is the computational input to the two rigidity statements [`CerednikDrinfeld.SpecialFormalODModule.exists_forall_not_hasStructureConstants_add_smul_eps_of_not_and`](thm.html#CerednikDrinfeld.SpecialFormalODModule.exists_forall_not_hasStructureConstants_add_smul_eps_of_not_and) and [`CerednikDrinfeld.SpecialFormalODModule.forall_not_hasStructureConstants_add_ite_smul_eps_of_forall_ne_add_smul`](thm.html#CerednikDrinfeld.SpecialFormalODModule.forall_not_hasStructureConstants_add_ite_smul_eps_of_forall_ne_add_smul), which rule out prescribed first-order shapes of structure constants; the uniqueness of the expansion used throughout is [`MvFormalGroup.CartierModule.existsUnique_eq_sum_verschiebungInt_iterate_homothety_add_of_charP`](thm.html#MvFormalGroup.CartierModule.existsUnique_eq_sum_verschiebungInt_iterate_homothety_add_of_charP).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal MvFormalGroup MvFormalGroup.CartierModule in

theorem CerednikDrinfeld.FormalODModule.hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q]
    (j₀ : Zp2 q →+* k) (X₀ : FormalODModule q k)
    (γ : Fin 2 → MvFormalGroup.CartierModule q X₀.F) (hγ : X₀.IsHomogeneousVBasis j₀ γ)
    (a : ℕ → Fin 2 → k) (ha : X₀.HasStructureConstants γ a)
    (γ' : Fin 2 → MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F)
    (hγ' : (X₀.map (algebraMap k (DualNumber k))).IsHomogeneousVBasis ((algebraMap k (DualNumber k)).comp j₀) γ')
    (s v w : Fin 2 → k) (g : Fin 2 → MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F)
    (hshape : ∀ i, γ' i =
      MvFormalGroup.CartierModule.homothety (Φ := (X₀.map (algebraMap k (DualNumber k))).F) (1 + s i • DualNumber.eps)
          (MvFormalGroup.CartierModule.baseChange (algebraMap k (DualNumber k)) (γ i) :
              MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := q) (Φ := (X₀.map (algebraMap k (DualNumber k))).F)))
          (MvFormalGroup.CartierModule.homothety (Φ := (X₀.map (algebraMap k (DualNumber k))).F) (v i • DualNumber.eps)
            (MvFormalGroup.CartierModule.baseChange (algebraMap k (DualNumber k)) (γ (FormalODModule.piIndex 0 i)) :
              MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F)) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := q) (Φ := (X₀.map (algebraMap k (DualNumber k))).F)))^[2]
          (MvFormalGroup.CartierModule.homothety (Φ := (X₀.map (algebraMap k (DualNumber k))).F) (w i • DualNumber.eps)
            (MvFormalGroup.CartierModule.baseChange (algebraMap k (DualNumber k)) (γ i) :
              MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F)) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := q) (Φ := (X₀.map (algebraMap k (DualNumber k))).F)))^[3] (g i))
    (a' : ℕ → Fin 2 → DualNumber k) (ha' : (X₀.map (algebraMap k (DualNumber k))).HasStructureConstants γ' a') :
    (∀ i, a' 0 i = algebraMap k (DualNumber k) (a 0 i) +
        ((s i - s (FormalODModule.piIndex 0 i)) * a 0 i) • DualNumber.eps) ∧
    (∀ i, a' 1 i = algebraMap k (DualNumber k) (a 1 i) +
        (v i * a 0 (FormalODModule.piIndex 0 i) - a 0 i ^ q * v (FormalODModule.piIndex 0 i) - a 1 i * s i) •
          DualNumber.eps) ∧
    (∀ i₀, a 0 i₀ = 0 →
      (∃ y : MvFormalGroup.CartierModule q X₀.F,
        MvFormalGroup.CartierModule.frobenius (γ i₀) = MvFormalGroup.CartierModule.verschiebungInt y) →
      a' 2 i₀ = algebraMap k (DualNumber k) (a 2 i₀) -
        (a 1 i₀ ^ q * v i₀ + a 2 i₀ * s (FormalODModule.piIndex 0 i₀)) • DualNumber.eps) := by sorry
