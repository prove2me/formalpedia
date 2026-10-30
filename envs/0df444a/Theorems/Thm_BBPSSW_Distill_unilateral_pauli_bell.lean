-- Prove2me | Theorems.Thm_BBPSSW_Distill_unilateral_pauli_bell
-- name    : BBPSSW.Distill.unilateral_pauli_bell
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:45:59.13261+00:00
-- url     : https://prove2.me/theorems/5f35eda9-fd22-4b41-b286-89bc06b3fe8c
-- title:
--   Unilateral Pauli rotations permute the Bell states
-- statement:
--   For each axis $a\in\{x,y,z\}$ and each Bell state $b$:
--
--   1. $(\sigma_a\otimes1)\,b=c\cdot\pi_a(b)$ for some phase $|c|=1$ (rotation of Alice's particle);
--   2. $(1\otimes\sigma_a)\,b=c'\cdot\pi_a(b)$ for some phase $|c'|=1$ (rotation of Bob's particle);
--   3. $\pi_a(b)\neq b$ (no state is left unchanged);
--   4. $\pi_a(\pi_a(b))=b$ (the states are exchanged in pairs),
--
--   where $\pi_x$: $\Psi^\pm\leftrightarrow\Phi^\pm$, $\pi_y$: $\Psi^\pm\leftrightarrow\Phi^\mp$, $\pi_z$: $\Psi^\pm\leftrightarrow\Psi^\mp$, $\Phi^\pm\leftrightarrow\Phi^\mp$ (`unilMap`).
--
--   These are the local corrections used in the breeding protocol.
--
--   Differences from the source:
--   - reading: we ignore overall phase changes → equality up to a factor c with |c| = 1; reason: the paper's phase convention
--   - generalization: a Pauli rotation of one particle → the stated action for a rotation of Alice's particle and for a rotation of Bob's particle; reason: the paper does not say which particle; either one specializes to the source
-- source:
--   Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, Purification of Noisy Entanglement and Faithful Teleportation via Noisy Channels, arXiv:quant-ph/9511027v2, p. 2, unnumbered bullet (unilateral Pauli rotations)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_BBPSSW_Distill_bellVec
import Definitions.Def_BBPSSW_Distill_pauli
import Definitions.Def_BBPSSW_Distill_unilMap

namespace BBPSSW.Distill

/-- **Unilateral Pauli rotations permute the Bell states.**
Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, *Purification of Noisy Entanglement
and Faithful Teleportation via Noisy Channels*, arXiv:quant-ph/9511027v2, p. 2 (unnumbered bullet): "Unilateral Pauli rotations (that is, rotations by π radians
about the x, y, or z axis) of one particle in an entangled pair. These operations map the Bell
states onto one another in a 1:1 pairwise fashion, leaving no state unchanged; thus σx maps
Ψ± ↔ Φ±; σz maps Ψ± ↔ Ψ∓ and Φ± ↔ Φ∓, while σy maps Ψ± ↔ Φ∓. We ignore overall phase changes
because they do not affect our arguments."

For each axis `a` and Bell state `b`:
1. `(σ_a ⊗ 1) b = c · unilMap a b` for some phase `|c| = 1` (rotation of Alice's particle);
2. `(1 ⊗ σ_a) b = c' · unilMap a b` for some phase `|c'| = 1` (rotation of Bob's particle);
3. `unilMap a b ≠ b` (no state is left unchanged);
4. `unilMap a (unilMap a b) = b` (the states are exchanged in pairs).

**Formalization Note.** "Ignoring overall phase" is the existential unit-modulus factor. The
statement covers a rotation of either particle (a generalization: the paper says "one
particle"). -/
theorem unilateral_pauli_bell (a : Axis) (b : BellLabel) :
    (∃ c : ℂ, ‖c‖ = 1 ∧
      QAlgorithms.act (Matrix.kronecker (pauli a) (1 : Matrix (Fin 2) (Fin 2) ℂ)) (bellVec b) =
        c • bellVec (unilMap a b)) ∧
    (∃ c : ℂ, ‖c‖ = 1 ∧
      QAlgorithms.act (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) (pauli a)) (bellVec b) =
        c • bellVec (unilMap a b)) ∧
    unilMap a b ≠ b ∧ unilMap a (unilMap a b) = b := by sorry

end BBPSSW.Distill
