-- Prove2me | Theorems.Thm_ConstDepthUnitary_three_query_synthesis
-- name    : ConstDepthUnitary.three_query_synthesis
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:48:45.43154+00:00
-- url     : https://prove2.me/theorems/ab95231f-c56e-4274-95a9-272567fe87ab
-- title:
--   Theorem 5.1 — three-query unitary synthesis
-- statement:
--   There is a universal constant $C$ such that for all $N$, every positive even $K$ and every traceless real symmetric unitary $S$ on $\mathbb C^N$,
--   $$\bigl\|S-i\,\hat E^\dagger\hat Q_S\hat F\hat Q_S\hat F\hat Q_S\hat E\bigr\|\le C\,N^{3/2}K^{3/4}e^{-\pi K/8}.$$
--   Moreover there is a universal constant $C_0$ such that, for every $\varepsilon>0$, the same quantity is at most $\varepsilon^2$ whenever $K\ge C_0\log(N/\varepsilon)$.
--
--   Thus three queries to a quadratic phase determined by $S$, with discrete Fourier transforms between them, implement $S$ on encoded states up to an error exponentially small in $K$.
--
--   Differences from the source:
--   - encoding: constants hidden in O(·) → an existential constant quantified before all data; reason: the paper's constants are universal
--   - generalization: K = 2^k → any positive even K; reason: footnote 15; it specializes to the printed case
--   - reading: K = Θ(log(N/ε)) for a sufficiently large constant → every even K with K ≥ C₀ log(N/ε), for every ε > 0; reason: it contains the upper end of the printed choice of K, so it is the stronger reading
-- source:
--   Nehoran, Slote, Yuen, All Unitaries Have Constant Depth Quantum Circuits, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Theorem 5.1, Eq. (55), p.25

import Mathlib
import Definitions.Def_ConstDepthUnitary_IsTRS
import Definitions.Def_ConstDepthUnitary_EHat
import Definitions.Def_ConstDepthUnitary_QHat
import Definitions.Def_ConstDepthUnitary_FHat
open scoped Matrix Matrix.Norms.L2Operator

namespace ConstDepthUnitary

/-- Theorem 5.1 (three-query unitary synthesis), Eq. (55): for a traceless real symmetric unitary `S`,
`‖S − i Ê† Q̂_S F̂ Q̂_S F̂ Q̂_S Ê‖ ≤ O(N^{3/2} K^{3/4} e^{−πK/8})`, with a universal constant. Moreover, `K ≥ C₀ log(N/ε)`
makes this at most `ε²`.

Nehoran, Slote, Yuen, *All Unitaries Have Constant Depth Quantum Circuits*, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Theorem 5.1, p.25.

**Formalization Note** `K` is any positive even integer (footnote 15). The "Moreover" is stated for every even `K` with
`C₀ log(N/ε) ≤ K`, which contains the printed `K = Θ(log(N/ε))` with a large enough constant. -/
theorem three_query_synthesis :
    (∃ C : ℝ, ∀ (N K : ℕ) (S : Matrix (Fin N) (Fin N) ℝ), Even K → 0 < K → IsTRS S →
      ‖S.map Complex.ofReal -
          Complex.I • ((EHat N K)ᴴ * QHat K S * FHat N K * QHat K S * FHat N K * QHat K S * EHat N K)‖ ≤
        C * (N : ℝ) ^ (3 / 2 : ℝ) * (K : ℝ) ^ (3 / 4 : ℝ) * Real.exp (-Real.pi * K / 8)) ∧
    (∃ C₀ : ℝ, ∀ (N K : ℕ) (S : Matrix (Fin N) (Fin N) ℝ) (ε : ℝ), Even K → 0 < K → IsTRS S → 0 < ε →
      C₀ * Real.log ((N : ℝ) / ε) ≤ K →
      ‖S.map Complex.ofReal -
          Complex.I • ((EHat N K)ᴴ * QHat K S * FHat N K * QHat K S * FHat N K * QHat K S * EHat N K)‖ ≤
        ε ^ 2) := by sorry

end ConstDepthUnitary
