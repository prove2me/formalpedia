-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_hasDetIndex_of_forall_mem_iff_exists_mulVec_eq_pow_smul
-- name    : CerednikDrinfeld.FormalOmega.hasDetIndex_of_forall_mem_iff_exists_mulVec_eq_pow_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/eccc1903-4fed-5ce4-ada8-902f0d76754a
-- title:
--   Determinant index of a lattice cut out by an integral matrix
-- statement:
--   Let $p$ be a prime, let $\gamma$ be a $2\times 2$ matrix over $\mathbb{Z}_p$, let $u\in\mathbb{Z}_p^{\times}$ and let $e,h$ be natural numbers with $\det\gamma = u\,p^{h}$. Let $N$ be a $\mathbb{Z}_p$-submodule of $\mathbb{Q}_p^{2}$ (that is, of $\mathrm{Fin}\,2\to\mathbb{Q}_p$) whose elements are characterised as follows: a vector $v$ lies in $N$ if and only if there are a natural number $m$ and vectors $w,c\in\mathbb{Z}_p^{2}$ such that $p^{m}\cdot v$ is the image of $w$ under the coordinatewise inclusion $\mathbb{Z}_p\hookrightarrow\mathbb{Q}_p$ and $\gamma w = p^{\,e+m}\cdot c$ in $\mathbb{Z}_p^{2}$. The conclusion is that $N$ has determinant index $2e-h$ with respect to the uniformiser $p$: there exists $g\in \mathrm{GL}_2(\mathbb{Q}_p)$ such that the image of the standard lattice $\{v : \text{all } v_i \text{ lie in } \mathbb{Z}_p\}$ under $v\mapsto g\,v$ equals $N$, and such that $\det g = u'\,p^{\,2e-h}$ in $\mathbb{Q}_p$ for some unit $u'\in\mathbb{Z}_p^{\times}$, the exponent $2e-h$ being taken as an integer power of $p$.
--
--   This is the lattice-theoretic bookkeeping behind Drinfeld's determinant condition on the lattices attached to a special formal module: a submodule described by the denominator-cleared condition $\gamma v \in p^{e}\mathbb{Z}_p^{2}$ is a $\mathbb{Q}_p$-translate of the standard lattice, with determinant valuation $2e-v_p(\det\gamma)$. It is used in the computation of the determinant index of the lattices arising from $\eta$-sections over geometric fibres in the Čerednik–Drinfeld setting, where it is applied in the cases of index $0$ and index $-1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_hasDetIndex_of_forall_mem_iff_exists_mulVec_eq_pow_smul.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.FormalOmega.hasDetIndex_of_forall_mem_iff_exists_mulVec_eq_pow_smul
    (p : ℕ) [Fact p.Prime] (γ : Matrix (Fin 2) (Fin 2) ℤ_[p]) (u : ℤ_[p]ˣ) (e h : ℕ)
    (hγ : γ.det = (u : ℤ_[p]) * (p : ℤ_[p]) ^ h)
    (N : Submodule ℤ_[p] (Fin 2 → ℚ_[p]))
    (hN : ∀ v : Fin 2 → ℚ_[p], v ∈ N ↔
      ∃ (m : ℕ) (w c : Fin 2 → ℤ_[p]),
        (p : ℚ_[p]) ^ m • v = (fun i => ((w i : ℤ_[p]) : ℚ_[p])) ∧
          γ.mulVec w = (p : ℤ_[p]) ^ (e + m) • c) :
    FormalOmega.HasDetIndex (K := ℚ_[p]) (p : ℤ_[p]) N (2 * (e : ℤ) - (h : ℤ)) := by sorry
