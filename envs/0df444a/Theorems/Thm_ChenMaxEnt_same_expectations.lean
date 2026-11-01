-- Prove2me | Theorems.Thm_ChenMaxEnt_same_expectations
-- name    : ChenMaxEnt.same_expectations
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:23:51.718519+00:00
-- url     : https://prove2.me/theorems/4de112ba-83a5-4f8b-8f82-1af92249e8d6
-- title:
--   §5.3 — under (31), $|\psi\rangle$ and the maximally mixed state return the same data
-- statement:
--   Let $F = (F_1,\dots,F_r)$ be Hermitian observables on $\mathcal H = \mathbb C^n$, let $V \subseteq \mathcal H$ be a subspace with orthonormal basis $|\psi_1\rangle,\dots,|\psi_m\rangle$ satisfying the **partial error-detecting condition**
--
--   $$
--   \langle\psi_a|F_i|\psi_b\rangle = 0 \qquad \text{for all } a \ne b \text{ and all } i, \tag{31}
--   $$
--
--   and put $|\psi\rangle = \frac{1}{\sqrt m}\sum_{a=1}^m |\psi_a\rangle$. Then the pure state $|\psi\rangle\langle\psi|$ and the maximally mixed state $\rho^* = P_V/m$ return the same measurement results:
--
--   $$
--   \operatorname{tr}\bigl(|\psi\rangle\langle\psi|\, F_i\bigr) = \operatorname{tr}(\rho^* F_i) \qquad (i = 1, \dots, r).
--   $$
--
--   This is the step of Observation 3 that places the pure limit state and the mixed state $\rho^*$ in the same linear family $L(\alpha)$.
--
--   Differences from the source:
--   - reading: "the same local density matrices" → the same data $\operatorname{tr}(\cdot\,F_i)$ for every $i$; reason: in Observation 3 the family $F$ is arbitrary, so its data are the only "local" information; for $F$ spanning the $k$-local operators the two coincide.
--   - reading: "a basis |ψa⟩ of V0" → an orthonormal family indexed by `Fin m` spanning $V$; reason: $|\psi\rangle$ is the limit (33) of unit vectors, hence a unit vector, which fails for non-orthogonal bases ($\psi_1 = e_0$, $\psi_2 = (e_0+e_1)/\sqrt2$ gives $\||\psi\rangle\|^2 = 1 + 1/\sqrt2$); (31) is the error-detecting condition of Knill–Laflamme, stated for orthonormal bases.
--   - encoding: $\langle\psi_a|F_i|\psi_b\rangle = \delta_{ab}$ for $a \ne b$ → $= 0$; reason: $\delta_{ab} = 0$ for $a \ne b$.
--   - generalization: the ground space $V_0$ of $H_0$ with $m > 1$ → any subspace $V$ spanned by an orthonormal family of any size $m$; reason: the identity does not involve the Hamiltonian; it specializes to the paper's case with $V = V_0$.
-- source:
--   Chen et al., Discontinuity of Maximum Entropy Inference and Quantum Phase Transitions, arXiv:1406.5046v2, §5.3, p.22 ("This condition guarantees that the state |ψ⟩ and the maximally mixed state ρ∗ have the same local density matrices"), eq. (31)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_ChenMaxEnt_expectations
import Definitions.Def_ChenMaxEnt_jointRange
import Definitions.Def_ChenMaxEnt_linearFamily
import Definitions.Def_ChenMaxEnt_maxEntInference
import Definitions.Def_ChenMaxEnt_groundEnergy
import Definitions.Def_ChenMaxEnt_groundSpace
import Definitions.Def_ChenMaxEnt_maximallyMixedOn

open QAlgorithms Filter Topology

namespace ChenMaxEnt

/-- Chen et al., arXiv:1406.5046v2, §5.3, p.22: "This condition guarantees that the state |ψ⟩
and the maximally mixed state ρ∗ have the same local density matrices." Here the condition is the
partial error-detecting condition (31), `⟨ψ_a|F_i|ψ_b⟩ = 0` for `a ≠ b` and every `F_i`, on an
orthonormal basis `(ψ_a)_{a=1}^m` of `V`, and `|ψ⟩ = m^{-1/2} Σ_a |ψ_a⟩`. Then `|ψ⟩⟨ψ|` and
`ρ* = P_V/m` return the same measurement results: `tr(|ψ⟩⟨ψ| F_i) = tr(ρ* F_i)` for every `i`.

**Formalization Note.** For an arbitrary family `F` "the same local density matrices" is read as
"the same data α" (for `k`-local `F` spanning the `k`-local operators the data are the `k`-RDMs).
The basis is orthonormal (`Orthonormal ℂ ψb`, indexed by `Fin m`) and spans `V`; the subspace `V`
is arbitrary (in the paper it is the ground space `V₀`), and `m` is any natural number. The inner
product is conjugate-linear in the first slot, so `⟨ψ_a|F_i|ψ_b⟩` is
`inner ℂ (ψb a) (toEuclideanLin (F i) (ψb b))`. -/
theorem same_expectations {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
    (F : ι → Matrix n n ℂ) (hF : ∀ i, (F i).IsHermitian) (V : Submodule ℂ (EuclideanSpace ℂ n))
    (m : ℕ) (ψb : Fin m → EuclideanSpace ℂ n) (hon : Orthonormal ℂ ψb)
    (hspan : Submodule.span ℂ (Set.range ψb) = V)
    (h31 : ∀ a b, a ≠ b → ∀ i, inner ℂ (ψb a) (Matrix.toEuclideanLin (F i) (ψb b)) = 0) :
    expectations F (pureDensity ((1 / Real.sqrt m : ℝ) • ∑ a, ψb a)) =
      expectations F (maximallyMixedOn V) := by sorry

end ChenMaxEnt
