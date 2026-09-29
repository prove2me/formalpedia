-- Prove2me | Theorems.Thm_FCP_BusyBeaver_busy_beaver_exceeds_computable
-- name    : FCP.BusyBeaver.busy_beaver_exceeds_computable
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T20:56:45.8116+00:00
-- url     : https://prove2.me/theorems/781f63b6-5470-43a4-9168-36baa41084d4
-- title:
--   The busy beaver function dominates every computable function (Radó)
-- statement:
--   **Radó's theorem (1962).** The busy beaver (maximum shifts) function is not bounded by any computable function: for every computable $f : \mathbb{N} \to \mathbb{N}$ there is an $n$ with $f(n) < \mathrm{BB}(n)$. In particular $\mathrm{BB}$ is not computable, which is why the individual values are so hard: $\mathrm{BB}(5) = 47\,176\,870$ was only settled in 2024 by the bbchallenge collaboration, and $\mathrm{BB}(6)$ is unknown.
--
--   *Formalization note:* the open question 'what is $\mathrm{BB}(6)$?' has no known answer to state as a theorem, so this mission records Radó's growth theorem instead, over an explicit two-symbol machine model fixed in the definition bundle.
-- source:
--   Formal Conjectures library (Google DeepMind), Apache-2.0, https://github.com/google-deepmind/formal-conjectures (FormalConjectures/BusyBeaver.lean); T. Radó, On non-computable functions, Bell System Tech. J. 41 (1962), 877--884

import Mathlib
import Definitions.Def_FCP_BusyBeaver

namespace FCP.BusyBeaver

theorem busy_beaver_exceeds_computable (f : ℕ → ℕ) (hf : Computable f) : ∃ n : ℕ, f n < BB n := by
  sorry

end FCP.BusyBeaver
