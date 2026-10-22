-- Prove2me | Theorems.Thm_EquivMapsEnt_Detect_theorem_5_1
-- name    : EquivMapsEnt.Detect.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:24:13.449344+00:00
-- url     : https://prove2.me/theorems/71594e25-d439-4304-a84a-2e691783b74d
-- title:
--   Theorem 5.1: equivariant t-positive maps detect every state detected by a given map
-- statement:
--   Fix integers $m,n,N,t$ with $1\le t\le\min\{m,n\}$, and let $\phi:M_n(\mathbb C)\to M_N(\mathbb C)$ be a $t$-positive complex linear map that is not completely positive. There exist dimensions $N_a$ and linear maps $\Phi_a:M_n(\mathbb C)\to M_{N_a}(\mathbb C)$, chosen together for all $a\ge1$, such that every $\Phi_a$ is unitarily equivariant and $t$-positive, $N_a\to\infty$, and
--
--   $$S_m(\Phi_{a+1})\subseteq S_m(\Phi_a),\qquad \bigcap_{a\ge1}S_m(\Phi_a)\subseteq S_m(\phi).$$
--
--   Hence any density matrix detected by $\phi$ eventually fails the detection test for every later member of this one equivariant family. The family may depend on the fixed ancillary dimension $m$.
--
--   **Formalization Note** Lean indexes the paper's $a\ge1$ family by $a\in\mathbb N$ starting at zero. Matrices on $\mathbb C^m\otimes\mathbb C^n$ use ancillary-first indices and $\Phi_a$ acts on the second factor. $t$-positivity itself implies Hermitian preservation, the section's standing convention, so no further binder is needed.
-- source:
--   Bardet, Collins & Sapra, Characterization of equivariant maps and application to entanglement detection, arXiv:1811.08193v3, p. 13, Theorem 5.1 and equation (18) (proof pp. 14–15)

import Definitions.Def_EquivMapsEnt_Detect_Basic

namespace EquivMapsEnt.Detect

open scoped Matrix ComplexOrder

/-- Theorem 5.1: an increasing-output sequence of unitary-equivariant t-positive detectors. -/
theorem theorem_5_1 (m n N t : ℕ)
    (φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin N) (Fin N) ℂ)
    (ht : 1 ≤ t) (htm : t ≤ m) (htn : t ≤ n)
    (hφ : IsTPositive t φ) (hnotCP : ¬ QAlgorithms.Entanglement.IsCompletelyPositive φ) :
    ∃ (Na : ℕ → ℕ)
      (Φ : (a : ℕ) → Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ]
        Matrix (Fin (Na a)) (Fin (Na a)) ℂ),
      (∀ a, IsUnitarilyEquivariant (Φ a)) ∧
      (∀ a, IsTPositive t (Φ a)) ∧
      Filter.Tendsto Na Filter.atTop Filter.atTop ∧
      (∀ a, detectionSet m (Φ (a + 1)) ⊆ detectionSet m (Φ a)) ∧
      (⋂ a, detectionSet m (Φ a)) ⊆ detectionSet m φ := by sorry

end EquivMapsEnt.Detect
