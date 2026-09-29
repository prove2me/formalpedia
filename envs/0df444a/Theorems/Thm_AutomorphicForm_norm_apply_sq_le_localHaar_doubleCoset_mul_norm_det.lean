-- Prove2me | Theorems.Thm_AutomorphicForm_norm_apply_sq_le_localHaar_doubleCoset_mul_norm_det
-- name    : AutomorphicForm.norm_apply_sq_le_localHaar_doubleCoset_mul_norm_det
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/1ba82f7d-5218-5da2-a6b6-937b518efa5c
-- title:
--   Entry bounds on a double coset KrhoK in GL₂(Kᵥ)
-- statement:
--   Let $K$ be a number field, let $v$ be a nonzero prime ideal of $\mathcal O_K$, let $K_v$ be the $v$-adic completion with its valuation ring $\mathcal O_v$ and normalised absolute value $\|\cdot\|$, and let $\rho \in GL_2(K_v)$ be arbitrary. Write $\mathcal K =$ [`AutomorphicForm.localIntegralSet K v`](def/AutomorphicForm_LocalOrbitalBase.html#L100) for the set of $g \in GL_2(K_v)$ such that both the matrix of $g$ and the matrix of $g^{-1}$ have all entries in $\mathcal O_v$, and let $\mu =$ [`AutomorphicForm.localHaar K v`](def/AutomorphicForm_LocalOrbitalBase.html#L168) be the Haar measure on $GL_2(K_v)$ (for the Borel $\sigma$-algebra of the topology) normalised by $\mu(\mathcal K) = 1$, obtained from $\mathcal K$ viewed as a positive compact set. Let $S = \mathcal K \cdot \{\rho\} \cdot \mathcal K$ be the pointwise product of sets, i.e. the double coset. The assertion is threefold: $1 \le \mu(S)$; $\mu(S) < \infty$; and every $g \in S$ satisfies $\|\det g\| = \|\det \rho\|$ together with the entrywise bound $\|g_{ij}\|^2 \le \mu(S) \cdot \|\det g\|$ for all $i, j \in \{0,1\}$, the measure being converted to a real number.
--
--   This is the elementary-divisor bookkeeping attached to the Cartan decomposition of $GL_2(K_v)$, stated without reference to the type $(a,b)$ of the double coset: the determinant norm is a double-coset invariant, the maximal entry norm is controlled by it, and the double coset carries finitely many but at least one right $\mathcal K$-coset. It is used in the archimedean-style estimates for automorphic forms on $GL_2$, namely in [`AutomorphicForm.exists_forall_norm_div_window_of_doubleCoset_apply_borel_mul_maximalCompact_ne_zero`](thm.html#AutomorphicForm.exists_forall_norm_div_window_of_doubleCoset_apply_borel_mul_maximalCompact_ne_zero), and is proved from the norm criterion for membership in $\mathcal K \,\mathrm{diag}(\pi^{m_1}, \pi^{m_2})\, \mathcal K$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_norm_apply_sq_le_localHaar_doubleCoset_mul_norm_det.lean

import Definitions.Def_AutomorphicForm_LocalOrbitalBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped Pointwise

theorem AutomorphicForm.norm_apply_sq_le_localHaar_doubleCoset_mul_norm_det
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (ρ : GL (Fin 2) (v.adicCompletion K)) :
    1 ≤ AutomorphicForm.localHaar K v
        (AutomorphicForm.localIntegralSet K v * ({ρ} : Set (GL (Fin 2) (v.adicCompletion K))) *
          AutomorphicForm.localIntegralSet K v) ∧
    AutomorphicForm.localHaar K v
        (AutomorphicForm.localIntegralSet K v * ({ρ} : Set (GL (Fin 2) (v.adicCompletion K))) *
          AutomorphicForm.localIntegralSet K v) < ⊤ ∧
    ∀ g ∈ AutomorphicForm.localIntegralSet K v * ({ρ} : Set (GL (Fin 2) (v.adicCompletion K))) *
        AutomorphicForm.localIntegralSet K v,
      ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ =
          ‖(ρ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ ∧
      ∀ i j : Fin 2,
        ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j‖ ^ 2 ≤
          (AutomorphicForm.localHaar K v
              (AutomorphicForm.localIntegralSet K v * ({ρ} : Set (GL (Fin 2) (v.adicCompletion K))) *
                AutomorphicForm.localIntegralSet K v)).toReal *
            ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ := by sorry
