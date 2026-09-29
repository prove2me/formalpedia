-- Prove2me | Theorems.Thm_AutomorphicForm_exists_generator_and_seq_mem_localCentralizer_tendsto_scalar_of_forall_not_diagonal
-- name    : AutomorphicForm.exists_generator_and_seq_mem_localCentralizer_tendsto_scalar_of_forall_not_diagonal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/b743f935-c730-56e6-8100-f61e53b8df5b
-- title:
--   Integral generator Y and depth-m elements c(1+varpi^m Y)
-- statement:
--   Let $K$ be a number field, $v$ a nonzero prime of $\mathcal O_K$ with completion $K_v$, $c \in K_v^\times$ a unit, and $\varpi \in K_v$ an element whose valuation is $\mathrm{ofAdd}(-1)$, i.e. a uniformiser. Let $\gamma_0 \in \mathrm{GL}_2(K_v)$ satisfy, first, that $\mathrm{tr}(\gamma_0)^2 - 4\det(\gamma_0)$ is a unit (the project's regular semisimplicity), and second, that for no $g \in \mathrm{GL}_2(K_v)$ do both off-diagonal entries of $g^{-1}\gamma_0 g$ vanish (non-split ellipticity). Then there exist a matrix $Y \in M_2(K_v)$ and a sequence $\gamma : \mathbb N \to \mathrm{GL}_2(K_v)$ such that: $v(\det Y) \le 1$ and $v(\mathrm{tr}\,Y) \le 1$; for every $b \in K_v$ with $v(b) \le 1$ it is not the case that both $v(\det(Y - b\cdot 1)) \le v(\varpi)^2$ and $v(\mathrm{tr}(Y - b \cdot 1)) \le v(\varpi)$ (no translate $(Y-b)/\varpi$ is integral); and for every $m \ge 1$, $\gamma_m$ commutes with $\gamma_0$, has $\mathrm{tr}(\gamma_m)^2 - 4\det(\gamma_m)$ a unit, satisfies $v(\det(c^{-1}\gamma_m)) = 1$ and $c^{-1}\gamma_m = 1 \cdot 1 + \varpi^m \cdot Y$ as matrices, and has centraliser of $\{\gamma_m\}$ equal to that of $\{\gamma_0\}$ in $\mathrm{GL}_2(K_v)$. Finally $\gamma_m$ tends, as $m \to \infty$, to the scalar matrix $c \cdot 1$ in $\mathrm{GL}_2(K_v)$.
--
--   This is the local construction underlying the elliptic germ computation at a finite place: $Y$ plays the role of a generator of the ring of integers of the quadratic algebra $K_v[\gamma_0]$, so that $\mathcal O_{K_v} \oplus \mathcal O_{K_v} Y$ is its maximal order, and the $\gamma_m = c(1 + \varpi^m Y)$ form a sequence of regular elements of the centraliser of $\gamma_0$ approaching the scalar $c$ at prescribed depth. It feeds the orbital-integral and transport statements [`AutomorphicForm.mul_measureReal_torusUnits_eq_neg_div_of_forall_isOrbitalIntegral_eq_add_nhds_scalar_of_forall_not_diagonal`](thm.html#AutomorphicForm.mul_measureReal_torusUnits_eq_neg_div_of_forall_isOrbitalIntegral_eq_add_nhds_scalar_of_forall_not_diagonal) and [`AutomorphicForm.exists_ellipticTransport_coupled_straighten_of_not_isSigmaConjugate_scalar_of_finrank_eq_two`](thm.html#AutomorphicForm.exists_ellipticTransport_coupled_straighten_of_not_isSigmaConjugate_scalar_of_finrank_eq_two), where the constancy of the centraliser and the convergence $\gamma_m \to c\cdot 1$ are used to transport Haar measure and to place $\gamma_m$ in a given neighbourhood of the scalar.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_generator_and_seq_mem_localCentralizer_tendsto_scalar_of_forall_not_diagonal.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain
open scoped TensorProduct
open scoped TensorProduct.RightActions

theorem AutomorphicForm.exists_generator_and_seq_mem_localCentralizer_tendsto_scalar_of_forall_not_diagonal
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (c : (v.adicCompletion K)ˣ) (ϖ : v.adicCompletion K)
    (hϖ : Valued.v ϖ = Multiplicative.ofAdd (-1 : ℤ))
    (γ₀ : GL (Fin 2) (v.adicCompletion K)) (_hreg : AutomorphicForm.IsRegularSemisimple γ₀)
    (_hns : ∀ g : GL (Fin 2) (v.adicCompletion K),
      ¬ (((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
         ((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0)) :
    ∃ (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) (γ : ℕ → GL (Fin 2) (v.adicCompletion K)),
      (Valued.v Y.det ≤ 1 ∧ Valued.v Y.trace ≤ 1) ∧
      (∀ b : v.adicCompletion K, Valued.v b ≤ 1 →
        ¬ (Valued.v (Y - b • 1).det ≤ Valued.v ϖ ^ 2 ∧ Valued.v (Y - b • 1).trace ≤ Valued.v ϖ)) ∧
      (∀ m : ℕ, 1 ≤ m →
        γ m ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
        AutomorphicForm.IsRegularSemisimple (γ m) ∧
        Valued.v ((((c⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) •
          ((γ m : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))).det) = 1 ∧
        ((c⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) •
            ((γ m : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
          = (1 : v.adicCompletion K) • 1 + (ϖ ^ m) • Y ∧
        AutomorphicForm.localCentralizer K v (γ m) = AutomorphicForm.localCentralizer K v γ₀) ∧
      Filter.Tendsto γ Filter.atTop (nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) := by sorry
