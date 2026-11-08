-- Prove2me | Theorems.Thm_AffDisp4n_theorem_4_1
-- name    : AffDisp4n.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T08:01:19.299985+00:00
-- url     : https://prove2.me/theorems/1f4c6c36-a5ae-4cbc-bfb9-123854ef99d3
-- title:
--   Theorem 4.1 (lower-bound clause; the algorithm: theorem_4_1_algorithm) — every $B_2$-circuit computing an affine disperser for dimension $d$ has at least $4n - 10d$ gates
-- statement:
--   Let $f : \mathbb F_2^n \to \mathbb F_2$ be an affine disperser for dimension $d$. Every $B_2$-circuit $C_0$ on $n$ inputs that computes $f$ has size
--   $$
--   |C_0| \ge 4n - 10d .
--   $$
--
--   This is the engine of the paper. With Li's affine dispersers for dimension $d = O(\log n)$ it gives the $4n - O(\log n)$ lower bound of Theorem 1.1. The previous best bound for affine dispersers was $3.1n - o(n)$ (Li–Yang).
--
--   **Formalization Note** The theorem's hypothesis that $f$ is computable in polynomial time is dropped, because the lower bound holds for every affine disperser. The algorithmic clause, a deterministic counterexample finder running in time $\mathrm{poly}(n, 2^d)$, is the companion item `AffDisp4n.theorem_4_1_algorithm`. The bound is stated in $\mathbb Z$, where $4n - 10d$ may be negative.
--
--   Differences from the source:
--   - generalization: f is an affine disperser for dimension d which is computable in polynomial time → f is an affine disperser for dimension d; reason: the lower-bound clause does not use the computability of f; the theorem for polynomial-time f is a special case
--   - generalization: B₂-circuit: input vertices are variables and constants, one gate of outdegree zero is the output, which may be a constant or a literal (p.13) → Circuit n: gates in a topological order, output a constant or a literal of any variable or gate, gates not reaching the output allowed; reason: this class contains every circuit of the paper with the same size, so the lower bound for it implies the paper's
--   - reading: Theorem 4.1: a deterministic algorithm finds a counterexample for |C₀| < 4n − 10d in time poly(n, 2ᵈ); in particular, any B₂-circuit computing f has size at least 4n − 10d → the "in particular" clause only; the algorithmic clause is the companion item AffDisp4n.theorem_4_1_algorithm; reason: Theorem 1.1 uses only this clause, and it needs no machine or encoding; the title names the companion
--   - encoding: size at least 4n − 10d → 4 * (n : ℤ) − 10 * d ≤ C₀.size; reason: integer arithmetic, since 4n − 10d may be negative
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §4, p.21, Theorem 4.1 (proof p.26)

import Mathlib
import Definitions.Def_AffDisp4n_Src
import Definitions.Def_AffDisp4n_Acyclic
import Definitions.Def_AffDisp4n_Acyclic_gateVal
import Definitions.Def_AffDisp4n_Acyclic_eval
import Definitions.Def_AffDisp4n_Circuit
import Definitions.Def_AffDisp4n_Circuit_Computes
import Definitions.Def_AffDisp4n_IsAffineDisperser

namespace AffDisp4n

/-- **Theorem 4.1, lower-bound clause** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), p.21; proof p.26): "In particular, any B₂-circuit C₀
computing f has size at least 4n − 10d", where `f : 𝔽₂ⁿ → 𝔽₂` is an affine disperser for dimension `d`.

**Formalization Note** The theorem's hypothesis "which is computable in polynomial time" is dropped: the
lower bound holds for every affine disperser. The algorithmic clause (a counterexample finder running in
time poly(n, 2ᵈ)) is the companion item `theorem_4_1_algorithm`. B₂-circuits are `Circuit n` (constant inputs allowed, the output a
constant or a literal of any variable or gate). The bound is in `ℤ`, where `4n − 10d` may be negative. -/
theorem theorem_4_1 {n : ℕ} (d : ℕ) (f : (Fin n → ZMod 2) → ZMod 2) (hf : IsAffineDisperser f d)
    (C₀ : Circuit n) (hC : C₀.Computes f) :
    4 * (n : ℤ) - 10 * d ≤ C₀.size := by sorry

end AffDisp4n
