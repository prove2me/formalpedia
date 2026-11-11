-- Prove2me | Theorems.Thm_FlowLatRound_theorem_1_1
-- name    : FlowLatRound.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:59:49.450102+00:00
-- url     : https://prove2.me/theorems/a9a68194-db81-4ce0-a62f-336f4734d03d
-- title:
--   Theorem 1.1 — random flow lattices: exact basis sampling in expected polynomial time, deterministic polynomial-time closest vectors, circumradius $\sqrt m/2$, and $\mathbb E\,\Phi(K)=\Theta(d^{5/4})$
-- statement:
--   For every $d\ge3$, let $\pi$ be drawn from the configuration model of degree $4$ on $n=d-1$ vertices tilted by the number of spanning trees ($m=2(d-1)$ edges), and let $K$ be the Voronoi cell of the flow lattice $\Lambda_{G(\pi)}$. Then:
--
--   1. every graph in the support has a flow lattice of rank $d$ and circumradius $R(K)=\sqrt m/2=\sqrt{2(d-1)}/2$, so all cells in the support have the same circumradius;
--   2. the basis sampler `sampleBasis d`, run on fair bits, halts with probability $1$, always outputs a pairing $\pi$ with a $\mathbb Z$-basis of $\Lambda_{G(\pi)}$, and outputs each $\pi$ with exactly its probability in the tilted model;
--   3. its expected bit cost is at most $c\,d^k$, with $c,k$ independent of $d$;
--   4. the deterministic decoder `flowCVP` returns a closest vector of $\Lambda_{G(\pi)}$ to every rational $y\in H_{G(\pi)}$, for every $\pi$ in the support, at bit cost at most $c\,(d+\mathrm{bits}(y))^k$;
--   5. with $c_0=1/(1072\sqrt2)$,
--   $$\frac{c_0}{2^{1/4}}\,d^{5/4}\le\mathbb E\,\Phi(K)\le3\,d^{5/4},$$
--   so $\mathbb E\,\Phi(K)=\Theta(d^{5/4})$.
--
--   The cube has $\Phi=d^{3/2}$; this is the first efficiently decodable lattice family that beats it by a polynomial factor, and it yields the replicable estimator of Corollary 1.2.
--
--   Differences from the source:
--   - encoding: (expected) polynomial time in the model of Appendix B (exact rational arithmetic, rejection sampling, expectation over the random choices) → a bit-cost counter (each operation charged (ratBits a + ratBits b + 1)^2, coin reads and list/array steps 1), a fair-coin tape with fuel-indexed halting, non-halting runs charged ⊤, expectation as ∫⁻ over the tape; polynomial = ∃ c k, one pair for all inputs; reason: a faithful rendering of Appendix B; the programs are named so the claim is about them
--   - generalization: "there is a distribution … such that a basis can be sampled exactly in expected polynomial time, closest vectors can be computed in deterministic polynomial time" → the named basis sampler sampleBasis (Lemma C.6 + fundamental cycles) and the named decoder flowCVP (Lemma C.3), with their exactness, correctness and cost bounds; reason: the proof's programs (p.9); specific programs imply the existence claims
--   - reading: "a polynomial-time minimum-cost flow algorithm" (Lemma C.3, unnamed) → successive shortest paths with Bellman–Ford after saturating all negative-cost unit arcs; reason: the decoder must be a defined program; any correct polynomial algorithm is acceptable, this one is fixed
--   - reading: order of the sampler's uniform draws not fixed (Lemma C.6) → slots one at a time; attachments vertex by vertex in the decoder's edge order; matching by least unmatched half-edge; reason: any order gives the same exact law; a program must fix one
--   - generalization: E Φ(K) = Θ(d^{5/4}) → (c₀/2^{1/4})·d^{5/4} ≤ E Φ(K) ≤ 3·d^{5/4} for every d ≥ 3, c₀ = 1/(1072√2); reason: the constants of the proofs (p.9 and p.28); explicit two-sided bounds for all d ≥ 3 imply Θ
--   - reading: closest vectors can be computed → for every rational target y ∈ H_{G(π)}; reason: Lemmas 3.1 and C.3 and the definition of CVP_Λ on H (§2) take rational y ∈ H_G
--   - generalization: all Voronoi cells in the support have the same circumradius → circumradius = √(2(d − 1))/2 = √m/2 for every π in the support; reason: a common explicit value implies "the same"
--   - encoding: flow lattices Λ of rank d; the support of the distribution → finrank H_{G(π)} = d; pairLaw π ≠ 0; reason: the rank of Λ_G is dim H_G; the support of a finite law
--   - encoding: volume V and surface area S of a convex body in H_G → Lebesgue measure in orthonormal coordinates of H_G (cellVol) and the Minkowski content lim_{s↓0}(V(K_s)−V(K))/s (cellSurf); reason: basis-independent normalization of Lebesgue measure; the Minkowski content equals the surface area of a convex body (Steiner formula, used in the proof of Lemma B.2)
--   - encoding: the tilted configuration model (P1)–(P3); edges of G(π) labeled by the pairs of π → processProb: the step probabilities of (P1)–(P3) summed over the outcomes producing (π, T); edges of G(π) enumerated by their smaller half-edge and oriented from it (pairLaw = marginal of π); reason: the law of the process itself; a relabeling or reorientation of edges is a signed coordinate permutation and changes no lattice, cell, τ or cycle length
--   - encoding: H_G = ker A_G with one vertex row of the incidence matrix deleted → kernel of the full n×m incidence map; reason: the rows of the full matrix sum to zero, so both kernels are equal
--   - encoding: vertices [n] and edges labeled 1..m → Fin n and Fin m (0-indexed); reason: Lean convention; relabeling changes no instance
-- source:
--   Chang, Replicable Mean Estimation via Random Lattice Rounding (manuscript, STOC 2027 submission, sha256 35bd3e4b…aeac), Theorem 1.1, pp.1–2 (PDF 3–4); proof p.9 (PDF 11) and pp.28–29 (PDF 30–31)

import Mathlib
import Definitions.Def_FlowLatRound_Sampler
import Definitions.Def_FlowLatRound_FlowCVP

namespace FlowLatRound

open MeasureTheory
open scoped ENNReal

/-- Chang, *Replicable Mean Estimation via Random Lattice Rounding* (manuscript, STOC 2027 submission,
sha256 35bd3e4b…aeac), Theorem 1.1 (Random flow lattices), pp.1–2 (PDF 3–4); proof p.9 (PDF 11) and
pp.28–29 (PDF 30–31). For every `d ≥ 3`, let `(π, T)` be drawn from the configuration model of
degree `4` on `n = d − 1` vertices tilted by the number of spanning trees (`m = 2(d − 1)` edges),
and `K` the Voronoi cell of the flow lattice `Λ_{G(π)}`:
* (a) every graph in the support has a flow lattice of rank `d` and circumradius `R(K) = √m/2`
  (so all cells in the support have the same circumradius);
* (b) the basis sampler `sampleBasis d` halts almost surely on fair bits, always outputs a pairing
  `π` together with a `ℤ`-basis of `Λ_{G(π)}`, and outputs each `π` with exactly its probability in
  the tilted model; its expected cost is at most `c d^k` (one `(c, k)` for all `d`);
* (c) the deterministic decoder `flowCVP` returns a closest vector of `Λ_{G(π)}` to every rational
  `y ∈ H_{G(π)}`, at cost at most `c (d + bits(y))^k` (one `(c, k)` for all `d`, `π`, `y`);
* (d) `(c₀/2^{1/4}) d^{5/4} ≤ E Φ(K) ≤ 3 d^{5/4}` with `c₀ = 1/(1072√2)`, i.e. `E Φ(K) = Θ(d^{5/4})`.

**Formalization Note.** "Polynomial time" is the bit-cost counter of Appendix B's model (operations
charged by operand bit length, fair coins at cost 1, rejection sampling); "expected" is the
lower Lebesgue integral over the fair-coin tape with non-halting runs charged `⊤`. The support is
`pairLaw π ≠ 0`. The constants of (d) are those of the proofs (p.9 and p.28). -/
theorem theorem_1_1 :
    (∀ d : ℕ, 3 ≤ d → ∀ π : (reg4 (d - 1)).Pairing, (reg4 (d - 1)).pairLaw π ≠ 0 →
      Module.finrank ℝ ((reg4 (d - 1)).graphOf π).flowSpace = d ∧
      circumradius ((reg4 (d - 1)).graphOf π).voronoiG = Real.sqrt (2 * ((d : ℝ) - 1)) / 2) ∧
    (∀ d : ℕ, 3 ≤ d →
      tape {ω | ¬ halts (sampleBasis d) ω} = 0 ∧
      (∀ ω out, outputOf (sampleBasis d) ω = some out →
        ∃ π : (reg4 (d - 1)).Pairing, ⇑π.1 = out.1 ∧
          IsZBasis ((reg4 (d - 1)).graphOf π).flowLattice out.2) ∧
      (∀ π : (reg4 (d - 1)).Pairing,
        tape {ω | ∃ B, outputOf (sampleBasis d) ω = some (⇑π.1, B)} =
          ENNReal.ofReal ((reg4 (d - 1)).pairLaw π))) ∧
    (∃ c k : ℕ, ∀ d : ℕ, 3 ≤ d →
      ∫⁻ ω, costOf (sampleBasis d) ω ∂tape ≤ (c : ℝ≥0∞) * (d : ℝ≥0∞) ^ k) ∧
    (∃ c k : ℕ, ∀ d : ℕ, 3 ≤ d → ∀ π : (reg4 (d - 1)).Pairing, (reg4 (d - 1)).pairLaw π ≠ 0 →
      ∀ y : Fin (reg4 (d - 1)).m → ℚ, ratVec y ∈ ((reg4 (d - 1)).graphOf π).flowSpace →
        intVec ((((reg4 (d - 1)).graphOf π).flowCVP y).run 0).1 ∈
            ((reg4 (d - 1)).graphOf π).flowLattice ∧
        (∀ z ∈ ((reg4 (d - 1)).graphOf π).flowLattice,
          ‖intVec ((((reg4 (d - 1)).graphOf π).flowCVP y).run 0).1 - ratVec y‖ ≤
            ‖z - ratVec y‖) ∧
        ((((reg4 (d - 1)).graphOf π).flowCVP y).run 0).2 ≤ c * (d + bitsQ y) ^ k) ∧
    (∀ d : ℕ, 3 ≤ d →
      1 / (1072 * Real.sqrt 2) / (2 : ℝ) ^ (1 / 4 : ℝ) * (d : ℝ) ^ (5 / 4 : ℝ) ≤
          (reg4 (d - 1)).EPhi ∧
        (reg4 (d - 1)).EPhi ≤ 3 * (d : ℝ) ^ (5 / 4 : ℝ)) := by sorry

end FlowLatRound
