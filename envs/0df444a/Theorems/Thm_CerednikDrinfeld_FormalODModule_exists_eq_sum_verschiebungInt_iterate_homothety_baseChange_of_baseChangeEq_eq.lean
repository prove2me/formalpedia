-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_eq_sum_verschiebungInt_iterate_homothety_baseChange_of_baseChangeEq_eq
-- name    : CerednikDrinfeld.FormalODModule.exists_eq_sum_verschiebungInt_iterate_homothety_baseChange_of_baseChangeEq_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/803fa95a-b71f-5db5-a78b-70e24e0a1479
-- title:
--   Digit shape of a homogeneous V-basis over k[ε]
-- statement:
--   Let $q$ be a prime and $k$ a field of characteristic $q$, let $j_0\colon W(\mathbb F_{q^2})\to k$ be a ring homomorphism, and let $X_0$ be a formal $\mathcal O_D$-module over $k$, i.e. a commutative two-dimensional formal group law $X_0.F$ together with an action of $W(\mathbb F_{q^2})$ by endomorphisms and an endomorphism $\varpi$ with $\varpi\circ\varpi=[q]$ and $\varpi\circ[a]=[\mathrm{Frob}\,a]\circ\varpi$. Assume the submodules `lieZero` and `lieOne` of the Lie algebra of $X_0$ attached to $j_0$ (the eigenspaces on which $[a]$ acts by $j_0(a)$, respectively by $j_0(\mathrm{Frob}\,a)$) are complementary, and let $\gamma_0,\gamma_1$ be a homogeneous $V$-basis of the Cartier module of $X_0.F$ for $j_0$: $\gamma_i$ lies in the graded piece of index $i$, meaning $[\tau(c)]$ acts on it as the homothety by $j_0(\tau(c))^{q^i}$ for all $c\in\mathbb F_{q^2}$ with $\tau$ the Teichmüller lift, and the matrix of tangent vectors $(\mathrm{tangent}(\gamma_i)_k)$ has invertible determinant. Write $X_\varepsilon$ for the base change of $X_0$ along $k\to k[\varepsilon]=k\oplus k\varepsilon$, and assume that pushing $X_\varepsilon.F$ forward along the projection $k[\varepsilon]\to k$ on the first coordinate returns $X_0.F$. Let $\gamma'$ be a homogeneous $V$-basis of the Cartier module of $X_\varepsilon.F$ for the composite $j_0$ followed by $k\to k[\varepsilon]$, whose base change along that projection is $\gamma$, i.e. `baseChangeEq` of $\gamma'_i$ equals $\gamma_i$ for each $i$. Then for every $i\in\{0,1\}$ and every $N\in\mathbb N$ there are coefficients $c_0,\dots,c_{N-1}\in k[\varepsilon]$ and an element $g$ of the Cartier module of $X_\varepsilon.F$ lying in the graded piece of index $i+N$, such that $$\gamma'_i=\sum_{m<N}V^m\bigl([c_m]\,\gamma^{\varepsilon}_{(m+i)\bmod 2}\bigr)+V^N g,$$ where $V$ is the integral Verschiebung `verschiebungInt`, $[c]$ denotes the homothety by $c$, $\gamma^{\varepsilon}_j$ is the base change of $\gamma_j$ along $k\to k[\varepsilon]$, and the index is `piIndex (m+1) i`; moreover the first component of $c_m$ in $k[\varepsilon]=k\oplus k\varepsilon$ is $1$ for $m=0$ and $0$ for $m\ge 1$.
--
--   This is the digit-expansion lemma describing, to any prescribed order $N$, the shape of a homogeneous $V$-basis of the Cartier module of the trivial first-order deformation $X_0\otimes_k k[\varepsilon]$ that reduces modulo $\varepsilon$ to a given homogeneous $V$-basis of $X_0$: the leading digit is $1$ modulo $\varepsilon$ and all later digits are divisible by $\varepsilon$. It feeds the analysis of structure constants of special formal $\mathcal O_D$-modules over $k[\varepsilon]$ in the Čerednik–Drinfeld part of the development, being used by the two results on the impossibility of prescribed $\varepsilon$-perturbations of structure constants.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_eq_sum_verschiebungInt_iterate_homothety_baseChange_of_baseChangeEq_eq.lean

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

theorem CerednikDrinfeld.FormalODModule.exists_eq_sum_verschiebungInt_iterate_homothety_baseChange_of_baseChangeEq_eq
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q]
    (j₀ : Zp2 q →+* k) (X₀ : FormalODModule q k)
    (hLie : IsCompl (X₀.lieZero j₀) (X₀.lieOne j₀))
    (γ : Fin 2 → MvFormalGroup.CartierModule q X₀.F) (hγ : X₀.IsHomogeneousVBasis j₀ γ)
    (hF : (X₀.map (algebraMap k (DualNumber k))).F.map (TrivSqZeroExt.fstHom k k k).toRingHom = X₀.F)
    (γ' : Fin 2 → MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F)
    (hγ' : (X₀.map (algebraMap k (DualNumber k))).IsHomogeneousVBasis ((algebraMap k (DualNumber k)).comp j₀) γ')
    (hred : ∀ i, MvFormalGroup.CartierModule.baseChangeEq (TrivSqZeroExt.fstHom k k k).toRingHom hF (γ' i) = γ i)
    (i : Fin 2) (N : ℕ) :
    ∃ (c : Fin N → DualNumber k) (g : MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F),
      g ∈ (X₀.map (algebraMap k (DualNumber k))).gradedPiece ((algebraMap k (DualNumber k)).comp j₀) (i + N) ∧
      γ' i =
        (∑ m : Fin N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := q) (Φ := (X₀.map (algebraMap k (DualNumber k))).F)))^[(m : ℕ)]
          (MvFormalGroup.CartierModule.homothety (c m)
            (MvFormalGroup.CartierModule.baseChange (algebraMap k (DualNumber k))
              (γ (FormalODModule.piIndex ((m : ℕ) + 1) i))))) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := q) (Φ := (X₀.map (algebraMap k (DualNumber k))).F)))^[N] g ∧
      (∀ m : Fin N, (m : ℕ) = 0 → TrivSqZeroExt.fst (c m) = 1) ∧
      (∀ m : Fin N, 1 ≤ (m : ℕ) → TrivSqZeroExt.fst (c m) = 0) := by sorry
