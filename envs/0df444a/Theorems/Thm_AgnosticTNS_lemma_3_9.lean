-- Prove2me | Theorems.Thm_AgnosticTNS_lemma_3_9
-- name    : AgnosticTNS.lemma_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:40:37.060636+00:00
-- url     : https://prove2.me/theorems/90fd0fbe-2b04-4f48-a60f-fecf6a7b242e
-- title:
--   Lemma 3.9 — efficient tomography
-- statement:
--   Given copies of an unknown state of rank at most $r$ on a $D$-dimensional Hilbert space, one can estimate the state to trace-norm error $\eta$ with failure probability at most $\beta$, using
--   $$
--   m=O\!\left(\frac{rD+\log(1/\beta)}{\eta^2}\right)
--   $$
--   copies and a number of elementary quantum gates and classical operations polynomial in $m$. The output is a classical description of a density operator.
--
--   This is the tomography routine used inside every Sub-Tomography call of the learner.
--
--   Differences from the source:
--   - encoding: an algorithm using copies, with gate count and classical time bounds → one learner family: a Clifford+T circuit on $\lceil\log_2 d\rceil$-qubit encodings of the copies plus ancillas, measured at the end, whose description is printed by a polynomial-time map; reason: house model of uniform quantum algorithms; the paper's learner measures copies jointly and adaptively, which a circuit with deferred measurements realises
--   - encoding: gates and classical operations polynomial in $m$ → the circuit is printed in polynomial time from the unary instance $(D,r,\lceil1/\eta\rceil,\lceil\log_2(1/\beta)\rceil)$, whose length is polynomial in $m$; reason: running time as a uniform printer; the instance length is at most polynomial in the bound $m$
--   - encoding: real $\eta,\beta$ → the instance carries $\lceil1/\eta\rceil$ and $\lceil\log_2(1/\beta)\rceil$; the guarantee is stated for the real $\eta,\beta$; reason: an algorithm's inputs are finite data; rounding changes the bound by a constant factor
--   - encoding: a classical description of a density operator → an output string that decodes (fixed decoder `decodeMat`) to a density matrix with Gaussian-rational entries; reason: finite-precision output; the decoder is fixed by the mission
--   - reading: an unknown rank-$r$ state → a state of rank at most $r$; reason: as in (2.11) and Corollary 2.7 ("a state of rank at most $r$")
--   - reading: trace-norm error $\eta$ (no range stated) → $\eta\in(0,1]$; reason: the standing convention for accuracy parameters ($\epsilon\in(0,1]$, p.11); every use ($\gamma_i$, $\gamma_{\mathrm{fin}}$, $\eta/(2\mu_u)$) is at most one
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Lemma 3.9, Eq. (3.67), p.26

import Mathlib
import Definitions.Def_AgnosticTNS_CopyLearner_prob
import Definitions.Def_AgnosticTNS_CopyLearner_code
import Definitions.Def_AgnosticTNS_decodeMat
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_traceNorm
open QAlgorithms.Complexity

namespace AgnosticTNS

/-- **Lemma 3.9 (Efficient tomography)**, p.26 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)). Given copies of an unknown rank-`r` state on a
`D`-dimensional Hilbert space, one can estimate the state to trace-norm error `η` with failure
probability at most `β`, using `m = O((rD + log(1/β))/η²)` copies (3.67) and a number of elementary
quantum gates and classical operations polynomial in `m`; the output is a classical description of a
density operator.

**Formalization Note** One uniform learner family indexed by `(D, r, ⌈1/η⌉, ⌈log₂(1/β)⌉)`, acting on
copies of a single `D`-dimensional "qudit" (`Fin 1 → Fin D`) encoded on `⌈log₂ D⌉` qubits; its
description is printed from the unary index by a polynomial-time map (so gates and classical
operations are polynomial in `m`); the output decodes, by the fixed decoder `decodeMat`, to a
density matrix with Gaussian-rational entries. -/
theorem lemma_3_9 :
    ∃ (Lr : CopyLearner (ℕ × ℕ × ℕ × ℕ) (fun _ => 1) (fun i => i.1)) (C : ℝ) (g : Str → Str),
      0 < C ∧ PolyTimeComputable g ∧
      ∀ (D r : ℕ) (η β : ℝ), 1 ≤ D → 1 ≤ r → 0 < η → η ≤ 1 → 0 < β → β < 1 →
        g (encNat D ++ encNat r ++ encNat ⌈1 / η⌉₊ ++ encNat ⌈Real.logb 2 (1 / β)⌉₊) =
            Lr.code (D, r, ⌈1 / η⌉₊, ⌈Real.logb 2 (1 / β)⌉₊) ∧
          (Lr.copies (D, r, ⌈1 / η⌉₊, ⌈Real.logb 2 (1 / β)⌉₊) : ℝ) ≤
            C * (r * D + Real.log (1 / β)) / η ^ 2 ∧
          ∀ ρ : Matrix (Fin 1 → Fin D) (Fin 1 → Fin D) ℂ, WildeQIT.IsDensityOperator ρ → ρ.rank ≤ r →
            1 - β ≤ Lr.prob (D, r, ⌈1 / η⌉₊, ⌈Real.logb 2 (1 / β)⌉₊) ρ (fun s =>
              ∃ M, decodeMat (Fin 1 → Fin D) s = some M ∧ WildeQIT.IsDensityOperator M ∧
                WildeQIT.traceNorm (M - ρ) ≤ η) := by sorry

end AgnosticTNS
