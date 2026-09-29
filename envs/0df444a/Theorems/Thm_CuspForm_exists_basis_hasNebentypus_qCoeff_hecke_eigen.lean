-- Prove2me | Theorems.Thm_CuspForm_exists_basis_hasNebentypus_qCoeff_hecke_eigen
-- name    : CuspForm.exists_basis_hasNebentypus_qCoeff_hecke_eigen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/c92eeef1-fca2-5ea5-adbc-dc4ca578a636
-- title:
--   Simultaneous eigenbasis for nebentypus and Hecke operators on Γ₁(N)
-- statement:
--   Let $N$ be a nonzero natural number and $k$ an integer. The assertion is the existence of a natural number $n$ and a basis $b : \mathrm{Fin}\,n \to S_k(\Gamma_1(N))$ of the complex vector space `CuspForm (Gamma1 N) k` of weight-$k$ cusp forms on $\Gamma_1(N)$ with the following property: for each index $i$ there is a Dirichlet character $\varepsilon$ modulo $N$ with values in $\mathbb{C}$ such that, first, $b_i$ has nebentypus $\varepsilon$ in the sense that for every $\gamma \in SL(2,\mathbb{Z})$ lying in $\Gamma_0(N)$ and every $\tau$ in the upper half-plane, $b_i(\gamma\cdot\tau) = \varepsilon(\gamma_{11} \bmod N)\,\bigl((\gamma_{10}\tau + \gamma_{11})^k\, b_i(\tau)\bigr)$, and, second, for every prime $p$ not dividing $N$ there is a scalar $\lambda \in \mathbb{C}$ with $$a_{pm}(b_i) + \varepsilon(p)\,p^{k-1}\,\bigl[\,p \mid m\,\bigr]\,a_{m/p}(b_i) = \lambda\, a_m(b_i) \quad \text{for all } m \in \mathbb{N},$$ where the bracket denotes the indicator of $p \mid m$ (the second term being $0$ otherwise) and $a_m(f)$ is [`ModularFormClass.qCoeff f m`](def/FLTPrelim_Modularity.html#L19), the $m$-th coefficient of the $q$-expansion of $f$ of width $1$ at $\infty$. In particular the existence of a basis indexed by a `Fin n` records that the space is finite-dimensional.
--
--   This is the simultaneous diagonalisability of the diamond operators $\langle d\rangle$ and of the Hecke operators $T_p$ for $p \nmid N$ on $S_k(\Gamma_1(N))$, stated concretely: a common eigenvector of the diamond operators is a form with a nebentypus, and for such a form the displayed coefficient relation expresses that it is a $T_p$-eigenform. It is one of the analytic inputs to the theory of newforms, and is used here to produce eigenforms from the coefficient conditions arising in the level-lowering and multiplicity-one arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_basis_hasNebentypus_qCoeff_hecke_eigen.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_PrimitiveFormGamma1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.exists_basis_hasNebentypus_qCoeff_hecke_eigen
    (N : ℕ) [NeZero N] (k : ℤ) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ (CuspForm (Gamma1 N) k)),
      ∀ i, ∃ ε : DirichletCharacter ℂ N, CuspForm.HasNebentypus ε (b i) ∧
        ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∃ lam : ℂ, ∀ m : ℕ,
          ModularFormClass.qCoeff (b i) (p * m) +
              ε (p : ZMod N) * (p : ℂ) ^ (k - 1) *
                (if p ∣ m then ModularFormClass.qCoeff (b i) (m / p) else 0) =
            lam * ModularFormClass.qCoeff (b i) m := by sorry
