-- Prove2me | Theorems.Thm_DirectedHamiltonicity_Main_finite_coin_weighted_parity_cutoff
-- name    : DirectedHamiltonicity.Main.finite_coin_weighted_parity_cutoff
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-26T15:24:33.716519+00:00
-- url     : https://prove2.me/theorems/4800be48-9cb0-4c51-8526-cbbdd5e23869
-- title:
--   Proposition 4: recovering every weighted path parity under a list cutoff and finite fair coins
-- statement:
--   Let $H$ be a normalized directed multigraph, with distinct endpoints $s,t$, and nonnegative weights with at most $d$ incoming weights per vertex. Write $n=|V|$ and take $M=(n+4)\lceil(2-2^{-d})^{n-2}\rceil$ trials, where the natural exponent is truncated at zero. An outcome in $\Omega$ consists of one common random augmentation and $M$ independent nonzero-coefficient tuples. At least $41/48$ of the outcomes both report at most $12M$ subsets with multiplicity and recover the parity for every integer target weight simultaneously by summing determinants over distinct reported subsets. For every $L$ with $2^L\ge40|\Omega|$, one can use $L$ fair bits to choose an outcome: each subset $U$ has at least $\lfloor2^L/|\Omega|\rfloor |U|$ preimages, and the probability of success is at least $5/6$. This theorem establishes finite sampling and algebraic correctness; the machine implementation and its runtime are a separate obligation.
-- source:
--   T. Koana and S. Kumabe, Breaking the 2^n barrier for directed hamiltonicity, STOC 2027 submission #811. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/811.pdf Proof of Proposition 4, PDF pp. 8–11, particularly p. 11. The finite-coin conversion and block constants are explicit refinements.

import Mathlib
import Definitions.Def_DirectedHamiltonicity_Main_DetSum

open Finset DirectedHamiltonicity.Main DirectedHamiltonicity.Main.Multidigraph Polynomial

open Classical in
theorem DirectedHamiltonicity.Main.finite_coin_weighted_parity_cutoff {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (H : Multidigraph V E) (w : E → ℕ) (s t : V) (hst : s ≠ t) (hn : H.IsNormalized w s t)
    (d : ℕ) (hd : 1 ≤ d) (deg : ∀ v, (H.incomingWeights w v).card ≤ d) :
    let n := Fintype.card V
    let M := ⌈(2-(1/2:ℝ)^d)^(n-2)⌉₊ * (n+4)
    let R := (i : Internal s t) → Finset (H.incomingWeights w i.1)
    let A := H.NonzeroCoeffs w s t
    let S := fun (r : R) (a : A) => H.sampled w s t (fun i => (a i).1) r
    let Ω := R × (Fin M → A)
    let good := univ.filter (fun q : R × (Fin M → A) =>
      (∑ j, (S q.1 (q.2 j)).card) ≤ 12*M ∧
      ∀ B : ℤ,
        (if B < 0 then (0 : ZMod 2) else
          (∑ x ∈ univ.biUnion (fun j => S q.1 (q.2 j)),
            (H.augLaplacian w s t x q.1).det).coeff B.toNat) =
          (H.weightedPathCount w s t B : ZMod 2))
    (41*Fintype.card Ω ≤ 48*good.card) ∧
      ∀ L : ℕ, 40*Fintype.card Ω ≤ 2^L →
        ∃ draw : (Fin L → Bool) → Ω,
          (∀ U : Finset Ω, (2^L/Fintype.card Ω)*U.card ≤
            (univ.filter (fun c => draw c ∈ U)).card) ∧
          5*2^L ≤ 6*(univ.filter (fun c => draw c ∈ good)).card := by sorry
