-- Prove2me | Theorems.Thm_CuspForm_exists_degeneracy_gamma1_hasNebentypus
-- name    : CuspForm.exists_degeneracy_gamma1_hasNebentypus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/791febdd-5fe6-50ce-b524-8772c85bdf61
-- title:
--   Degeneracy map g(dτ) from level M to level N
-- statement:
--   Let $k$ be an integer and $M,N,d$ natural numbers with $N$ nonzero, and suppose $M d \mid N$ (so in particular $d \neq 0$ and $M \mid N$). Given a cusp form $g$ of weight $k$ on $\Gamma_1(M)$, the theorem asserts the existence of a cusp form $G$ of weight $k$ on $\Gamma_1(N)$ with three properties. First, $G$ is pointwise the pullback of $g$ along the scaling matrix [`ModularForm.heckeDiagMatrix d`](def/ModularForm_HeckeOperator.html#L21), the element $\mathrm{diag}(d,1)$ of $\mathrm{GL}_2(\mathbb{R})$: for every $\tau$ in the upper half-plane, $G(\tau) = g(d\tau)$. Second, its $q$-expansion coefficients at $1$ are those of $g$ spread out by $d$: for every natural number $n$, the $n$-th coefficient of $G$ equals the $(n/d)$-th coefficient of $g$ when $d \mid n$, and $0$ otherwise. Third, $G$ inherits the nebentypus of $g$ raised to level $N$: for every Dirichlet character $\varepsilon$ modulo $M$ such that $g(\gamma \cdot \tau) = \varepsilon(\gamma_{11}) (\gamma_{10}\tau + \gamma_{11})^{k} g(\tau)$ for all $\gamma \in \Gamma_0(M)$ and all $\tau$, the same transformation law holds for $G$ with respect to all $\gamma \in \Gamma_0(N)$ and the character modulo $N$ obtained from $\varepsilon$ by `DirichletCharacter.changeLevel` along $M \mid N$.
--
--   This is the degeneracy (oldform) map $\iota_d : S_k(\Gamma_1(M)) \to S_k(\Gamma_1(N))$, $g \mapsto g(d\tau)$, for $Md \mid N$, together with its effect on $q$-expansions and on nebentypus characters. It is the mechanism by which eigenforms of level $M$ are transported to level $N$ with unchanged Hecke eigenvalues away from $N$, and it is used downstream in the comparison of eigenforms of different levels and in the identification of Frobenius characteristic polynomials attached to eigenpackets.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_degeneracy_gamma1_hasNebentypus.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_PrimitiveFormGamma1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.exists_degeneracy_gamma1_hasNebentypus
    {k : ℤ} {M N d : ℕ} [NeZero N] (hd : M * d ∣ N) (g : CuspForm (Gamma1 M) k) :
    ∃ G : CuspForm (Gamma1 N) k,
      (∀ τ : UpperHalfPlane, G τ = g (ModularForm.heckeDiagMatrix d • τ)) ∧
      (∀ n : ℕ, ModularFormClass.qCoeff G n =
        if d ∣ n then ModularFormClass.qCoeff g (n / d) else 0) ∧
      ∀ ε : DirichletCharacter ℂ M, CuspForm.HasNebentypus ε g →
        CuspForm.HasNebentypus (DirichletCharacter.changeLevel (dvd_of_mul_right_dvd hd) ε) G := by sorry
