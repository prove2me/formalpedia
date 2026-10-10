-- Prove2me | Theorems.Thm_ConleyZehnder_czIndex_locally_constant
-- name    : ConleyZehnder.czIndex_locally_constant
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T22:22:59.856418+00:00
-- url     : https://prove2.me/theorems/5fcb541e-a386-4acb-a432-64938c176f63
-- title:
--   The Conley–Zehnder index is locally constant on SP(n)
-- statement:
--   Let $\mathrm{SP}(n)$ be the set of continuous paths $\psi:[0,1]\to\mathrm{Sp}(2n)$ with $\psi(0)=\mathrm{Id}$ and $\det(\mathrm{Id}-\psi(1))\neq 0$ (Gutt, Definition 4), viewed as a subspace of $C([0,1],\mathbb R^{2n\times 2n})$ with the compact-open (equivalently, uniform) topology, and let $\mu_{CZ}$ be the Conley–Zehnder index (Gutt, Definition 7 and Corollary 12).
--
--   For every $\psi\in\mathrm{SP}(n)$ there is a neighbourhood $U$ of $\psi$ in $C([0,1],\mathbb R^{2n\times 2n})$ such that $\mu_{CZ}(\psi')=\mu_{CZ}(\psi)$ for every $\psi'\in U\cap\mathrm{SP}(n)$. In other words, $\mu_{CZ}$ is locally constant on $\mathrm{SP}(n)$.
--
--   This is the local form of the homotopy property of the index (Gutt, Proposition 8 (2)); it gives constancy of $\mu_{CZ}$ on connected components of $\mathrm{SP}(n)$ and stability of the index under small perturbations of a path.
--
--   Formalization note: `SP`, `czIndex` and `Mat n` come from the definition module `ConleyZehnder_Setting`; the topology on `C(unitInterval, Mat n)` is Mathlib's compact-open topology. "Close enough" is the filter statement `∀ᶠ ψ' in 𝓝 ψ, ψ' ∈ SP n → czIndex ψ' = czIndex ψ`.
-- source:
--   Gutt, Generalized Conley-Zehnder index, Ann. Fac. Sci. Toulouse Math. 23 (2014) 907-932, https://doi.org/10.5802/afst.1430 (arXiv:1307.7239), Proposition 8 (2) (homotopy), local form

import Definitions.Def_ConleyZehnder_Setting

namespace ConleyZehnder

open Filter Topology

/-- `μ_CZ` is locally constant on `SP(n)`: every path `ψ' ∈ SP(n)` close enough to
`ψ ∈ SP(n)` in `C([0, 1], ℝ^{2n×2n})` (compact-open topology) has the same
Conley–Zehnder index as `ψ`. -/
theorem czIndex_locally_constant {n : ℕ} (ψ : C(unitInterval, Mat n)) (hψ : ψ ∈ SP n) :
    ∀ᶠ ψ' in 𝓝 ψ, ψ' ∈ SP n → czIndex ψ' = czIndex ψ := by sorry

end ConleyZehnder
