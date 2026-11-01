-- Prove2me | Theorems.Thm_CollectiveDFS_conj_mem_exchangeLie
-- name    : CollectiveDFS.conj_mem_exchangeLie
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:03:01.278038+00:00
-- url     : https://prove2.me/theorems/362d99bd-6f30-4370-85cc-b7cf7b506dda
-- title:
--   (4.6), p.11 — conjugation by unitary evolution stays in the Lie closure
-- statement:
--   Let $H$ and $K$ be Hamiltonians obtained from exchange, i.e. $iH,iK\in\mathfrak g_n$, and let $t$ be real. With $U=e^{-itH}$, the transformed Hamiltonian $UKU^\dagger$ of (4.6) is again obtained from exchange by scalar multiplication, addition and commutators alone:
--   $$i\,e^{-itH}Ke^{itH}\in\mathfrak g_n.$$
--
--   Hence composition law 4 (conjugation by unitary evolution) adds nothing to laws 1–3 for exchange Hamiltonians, which is why Theorem 5 can be stated with the Lie closure only.
--
--   Differences from the source:
--   - reading: if a gate U and its inverse U† can be implemented, any implementable Hamiltonian H can be modified to H_eff = U H U† → for U = exp(−itH) with H implementable, U K U† is again in the Lie closure; reason: in the exchange-only model the implementable gates are evolutions under implementable Hamiltonians; the statement is that law 4 does not enlarge the Lie closure, the form the proof of Theorem 5 needs at (7.31)
-- source:
--   Kempe, Bacon, Lidar & Whaley, Theory of Decoherence-Free Fault-Tolerant Universal Quantum Computation, arXiv:quant-ph/0004064v2, §IV.B, composition law 4, eq. (4.6), p.11

import Mathlib
import Definitions.Def_CollectiveDFS_exchangeLie

open QAlgorithms

namespace CollectiveDFS

/-- Composition law 4, eq. (4.6) (Kempe, Bacon, Lidar & Whaley, arXiv:quant-ph/0004064v2, §IV.B, p.11, PDF p.11): conjugation by unitary evolution.
If `H` and `K` are obtained from exchange (`i H, i K ∈ exchangeLie n`) and `t` is real, then the
transformed Hamiltonian `U K U†` with `U = exp(−itH)` is again obtained from exchange by scalar
multiplication, addition and commutators alone.

**Formalization Note** `NormedSpace.exp` is the matrix exponential; `exp(itH)` is `U† = U⁻¹`.
That `H` is Hermitian follows from `i H ∈ exchangeLie n` and is not assumed. This is the reason
the closure `exchangeLie` omits law 4. -/
theorem conj_mem_exchangeLie (n : ℕ) (H K : Matrix (Qubits n) (Qubits n) ℂ)
    (hH : Complex.I • H ∈ exchangeLie n) (hK : Complex.I • K ∈ exchangeLie n) (t : ℝ) :
    Complex.I • (NormedSpace.exp ((-(Complex.I * (t : ℂ))) • H) * K *
      NormedSpace.exp ((Complex.I * (t : ℂ)) • H)) ∈ exchangeLie n := by sorry

end CollectiveDFS
