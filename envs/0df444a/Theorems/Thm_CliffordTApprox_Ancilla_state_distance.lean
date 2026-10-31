-- Prove2me | Theorems.Thm_CliffordTApprox_Ancilla_state_distance
-- name    : CliffordTApprox.Ancilla.state_distance
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T02:29:51.067542+00:00
-- url     : https://prove2.me/theorems/bfe6c9c6-8fb3-49ed-affb-437e8df058c9
-- title:
--   §2.2, p. 3 — a controlled preparation of |v⟩ is within √(2/4^k + 2√2/2^k) of Λ(e^{iφ}) ⊗ |00⟩ (the page: O(1/2^{0.5k}))
-- statement:
--   Let $k \in \mathbb N$, $0\le\varphi\le\pi/4$, let $a,b,c,d$ be integers with $a^2+b^2+c^2+d^2 = 4^k - \lfloor 2^k\cos\varphi\rfloor^2 - \lfloor 2^k\sin\varphi\rfloor^2$, and let $|v\rangle$ be the corresponding unit vector. Let $W$ be any operator on three qubits (data qubit first, then two ancillas) that is a controlled preparation of $|v\rangle$:
--   $$W|0\rangle|w\rangle = |0\rangle|w\rangle\ \text{for every two-qubit }|w\rangle, \qquad W|1\rangle|00\rangle = |1\rangle|v\rangle .$$
--   Consider the linear maps from one qubit to three qubits
--   $$\mathcal W : \psi \mapsto W(\psi\otimes|00\rangle), \qquad \mathcal I : \psi \mapsto (\Lambda(e^{i\varphi})\psi)\otimes|00\rangle .$$
--   Then their Frobenius distance satisfies
--   $$\|\mathcal W - \mathcal I\|_F \le \sqrt{\frac{2}{4^k} + \frac{2\sqrt 2}{2^k}} .$$
--
--   Since the Frobenius norm dominates the operator norm, every input $\alpha|0\rangle + \beta|1\rangle$ with $|\alpha|^2+|\beta|^2 = 1$ is mapped to within this distance of $\alpha|000\rangle + \beta e^{i\varphi}|100\rangle$, which is the paper's estimate $O(1/2^{0.5k})$.
--
--   **Formalization Note.** $W$ need not be unitary; its data-$0$ branch is fixed for every ancilla input, as required of a controlled operator. The distance bound uses only its action on the two inputs with ancillas $|00\rangle$. The constants are pinned from the page's display $\sqrt{|\beta(e^{i\varphi}-\gamma)|^2 + |\beta|^2\||g\rangle\|^2}$ with $|\gamma - e^{i\varphi}|\le\sqrt2/2^k$ and $\||g\rangle\|^2 = 1-|\gamma|^2 \le 2\sqrt2/2^k$. The page prints the third term of the transformed state as $\beta|01\rangle\otimes|g\rangle$; by its own definition $|v\rangle = \gamma|00\rangle + |1\rangle\otimes|g\rangle$ it is $\beta|1\rangle\otimes|1\rangle\otimes|g\rangle$, which is what this statement uses.
-- source:
--   Kliuchnikov, Maslov, Mosca, Asymptotically optimal approximation of single qubit unitaries by Clifford and T circuits using a constant number of ancillary qubits, arXiv:1212.0822v2, p. 3, §2.2

import Mathlib
import Definitions.Def_CliffordTApprox_Ancilla_Setting

namespace CliffordTApprox.Ancilla

open QAlgorithms
open QAlgorithms.Papers.Independent.Renew46.P12

/-- §2.2, p. 3: if `W` acts as the controlled preparation of `|v⟩` (with `(a, b, c, d)` solving
the four-square equation and `0 ≤ φ ≤ π/4`), then the initialized map of `W` is within Frobenius
distance `√(2/4^k + 2√2/2^k)` (the page: `O(1/2^{0.5k})`) of `Λ(e^{iφ}) ⊗ |00⟩`. -/
theorem state_distance (k : ℕ) (φ : ℝ) (hφ₀ : 0 ≤ φ) (hφ₁ : φ ≤ Real.pi / 4)
    (a b c d : ℤ) (habcd : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = deficit k φ)
    (W : Matrix (Qubits (1 + 2)) (Qubits (1 + 2)) ℂ)
    (hW : PreparesControlled W (vecV k φ a b c d)) :
    frobNorm (initializedMap W - idealMap (phaseGate φ) 2) ≤
      Real.sqrt (2 / 4 ^ k + 2 * Real.sqrt 2 / 2 ^ k) := by sorry

end CliffordTApprox.Ancilla
