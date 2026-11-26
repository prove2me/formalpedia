-- Prove2me | Theorems.Thm_Arxiv2405_00432_orthogonal_states_calibration
-- name    : Arxiv2405_00432.orthogonal_states_calibration
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-26T12:52:36.227335+00:00
-- url     : https://prove2.me/theorems/e825c918-844f-5bc0-a6d8-627d6fce46d0
-- title:
--   Eq. (8): the orthogonal calibration states give zero intensity in their own quadrant
-- statement:
--   Let $|\phi_i\rangle$ be the POVM states of eq. (1), $\hat\pi_i=\tfrac12|\phi_i\rangle\langle\phi_i|$, and $|\bar\phi_i\rangle$ the calibration states of eq. (8). Then for each $i\in\{1,2,3,4\}$:
--
--   1. $\langle\bar\phi_i|\phi_i\rangle=0$;
--   2. $P_i(\bar\phi_i)=\langle\bar\phi_i|\hat\pi_i|\bar\phi_i\rangle=0$, so an ideal device illuminated with $|\bar\phi_i\rangle$ records no intensity in quadrant $i$;
--   3. the other three outcomes have equal probabilities: $P_j(\bar\phi_i)=P_k(\bar\phi_i)$ for all $j,k\neq i$.
--
--   These states are used to calibrate the interferometer and to test its stability.
-- source:
--   McWilliam, Al Khafaji, Svensson, Pádua and Franke-Arnold, Dynamic Mueller matrix polarimetry using generalized measurements, arXiv:2405.00432v1 (2024), claim c004; Section 3.2, eq. (8) and the sentence after it, PDF p. 6

import Mathlib
import Definitions.Def_Arxiv2405_00432_Basic

open Matrix

namespace Arxiv2405_00432

theorem orthogonal_states_calibration :
    (∀ i : Fin 4, star (orthState i) ⬝ᵥ povmState i = 0) ∧
    (∀ i : Fin 4, outcomeProb i (orthState i) = 0) ∧
    (∀ i j k : Fin 4, j ≠ i → k ≠ i → outcomeProb j (orthState i) = outcomeProb k (orthState i)) := by sorry

end Arxiv2405_00432
