-- Prove2me | Theorems.Thm_BilatMatch_Supplement_theorem_B_14
-- name    : BilatMatch.Supplement.theorem_B_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:31:59.482036+00:00
-- url     : https://prove2.me/theorems/b00af26c-ec05-44c1-b92d-bd9bf5be6249
-- title:
--   Theorem B.14 (Market-Level Targets) — $V_\alpha(\mathcal I)\ge T_\alpha(\mathcal I)$, and $T_\alpha(\mathcal I)\ge\sum_e\beta_e\mathrm{FB}_e$ for the envelope targets
-- statement:
--   Consider a matching market $\mathcal I$ with finitely many agents, independent finitely supported priors and downward-closed feasibility, in which every seller is $\alpha$-weakly regular ($\alpha\ge0$), and the canonical first-best matching $M^*$. For each edge $e=(i,j)$ with possible positive surplus let $T^r_{e,\ell}$ be a table satisfying Theorem B.11 on $e$'s endpoint priors and buyer support, and put
--   $$T_\alpha(\mathcal I)=\sum_{e=(i,j)}\mathbb E_\omega\Big[\sum_\ell f_{B_i}(v^\ell_i)\,T^{r_{e,\omega}(\ell)}_{e,\ell}\Big],$$
--   where $r_{e,\omega}(\ell)$ is the number of seller types at which $M^*$ selects $e$ when buyer $i$ reports $v^\ell_i$. Then
--
--   1. $V_\alpha(\mathcal I)\ge T_\alpha(\mathcal I)$ for every such table;
--   2. for the envelope targets $T^r_\ell=\min_{r'\ge r}\beta_{r'}B^{r'}_\ell$, $T^0_\ell=0$ of (26),
--   $$T_\alpha(\mathcal I)\ \ge\ \sum_e\beta_e\,\mathrm{FB}_e,$$
--   with $\beta_e$ the minimum of the bilateral factors $\beta_r$ of (25) on $e$'s priors and $\mathrm{FB}_e=\mathbb E[(v_i-c_j)\mathbf 1\{e\in M^*\}]$.
--
--   The benchmark $T_\alpha(\mathcal I)$ distinguishes edges and seller caps, so it can exceed the uniform bound $\min_e\beta_e\cdot\mathrm{FB}(\mathcal I)$.
--
--   **Formalization Note** $V_\alpha(\mathcal I)$ uses the agents' finite supports as report domains (the composition convention of §3.1).
--
--   Differences from the source:
--   - encoding: V_α(I) of a finite market (composition conventions of §3.1, p.37) → ValphaOn I (suppDomain I) α: BIC/IIR for types and reports in each agent's finite support; reason: the report-domain convention the paper states for the composition statements, as in base Theorem 3.2 and Theorem B.10
--   - encoding: a table T^r_{e,ℓ} satisfying Theorem B.11 on e's original endpoint priors and buyer support → IsB11Table: on the prefix caps κ_r of each edge with possible positive surplus, T nonnegative, nondecreasing in r, T^0 = 0, and condition (i) of Theorem B.11; reason: for a finitely supported seller the caps are exactly the prefixes κ_r and the only zero-mass cap is κ_0 = ∅; condition (i) is equivalent to (ii) by Theorem B.11
--   - encoding: β_r (eq. (25)), a real number in [0, 1 + α] → the EReal infimum of V_α/FB over positive weight vectors, converted to ℝ; reason: under v^n > c^1 every denominator is positive and the infimum is finite (p.39)
--   - encoding: sums over e = (i, j) (edges with possible positive surplus for T_α; all edges for ∑_e β_e FB_e) → sums over posEdges I (some buyer atom exceeds some seller atom); reason: an edge without possible positive surplus is never selected by M* (fewest edges), so its terms are 0 and β_e is defined only on posEdges
--   - encoding: indices v^1 < ⋯ < v^n, c_1 < ⋯ < c_m → sortedAtom from index 0; κ_r = first r atoms; reason: Lean indexing
--   - encoding: the canonical first-best matching M* with a fixed tie order → firstBestMatching I rank for every rank with IsTieOrder; reason: the statement holds for each fixed order
--   - encoding: every seller α-weakly regular (finite priors) → IsAlphaWeaklyRegular α F (atoms F) (alphaVirtualCost α F); reason: the published definition with the finite-prior domain and α-virtual cost
-- source:
--   Liu, Qin, Wang, From Bilateral Trade to Matching Markets: Sharp Gains from Trade, arXiv:2609.30702 (held version, sha256 ff1490adbe231952acc5fc467ea7dfe37f237d7ce95248cd45c10451aedf4984), Theorem B.14, p.40 (pdf p.42), with the market-level benchmark pp.39–40 (pdf pp.41–42) and eqs. (25)–(26), App. B.3.2, pp.38–39

import Mathlib
import Definitions.Def_BilatMatch_InX
import Definitions.Def_BilatMatch_sellerCost
import Definitions.Def_BilatMatch_Supplement_marketTarget

open MeasureTheory

namespace BilatMatch.Supplement

open BilatMatch

/-- **Theorem B.14 (market-level targets).** Liu, Qin, Wang, *From Bilateral Trade to Matching
Markets: Sharp Gains from Trade*, arXiv:2609.30702 (held version, sha256 ff1490ad…), Theorem B.14,
p.40 (pdf p.42), with the setting and definitions of "The Market-Level Benchmark", pp.39–40, and
App. B.3.2, pp.38–39 (eqs. (25), (26)).

Consider a matching market `I` with finitely many agents, independent finitely supported priors and
downward-closed feasibility, in which every seller is `α`-weakly regular, and the canonical
first-best matching `M*` (any fixed tie order). Then:
1. for every table `T^r_{e,ℓ}` satisfying Theorem B.11 on each edge with possible positive surplus
   (on its original endpoint priors and buyer support), `V_α(I) ≥ T_α(I)`;
2. for the envelope targets (26), `T_α(I) ≥ ∑_e β_e FB_e`.

**Formalization Note**
* `V_α(I)` is `ValphaOn I (suppDomain I) α`: reports range over each agent's finite support, the
  report-domain convention of §3.1 used for the composition statements (p.37).
* Seller `j` is `α`-weakly regular in the published sense with domain its atoms and `τ^α` its finite
  `α`-virtual cost (eq. (2)).
* `T_α(I)`, `r_{e,ω}(ℓ)`, `β_r`, the targets (26), `β_e`, `FB_e` are `marketTarget`, `prefixCount`,
  `betaR`, `envelopeTable`, `betaE`, `FBe`; "satisfying Theorem B.11" is `IsB11Table` (the hypotheses
  of Theorem B.11 and its condition (i) on the prefix caps). Sums run over the edges with possible
  positive surplus; the other edges are never selected by `M*`. -/
theorem theorem_B_14 (α : ℝ) (hα : 0 ≤ α) {B S : Type*} [Fintype B] [Fintype S]
    (I : Market B S) (hI : I.IsValid) (hfinB : ∀ i, IsFiniteSupport (I.buyerLaw i))
    (hfinS : ∀ j, IsFiniteSupport (I.sellerLaw j))
    (hreg : ∀ j, IsAlphaWeaklyRegular α (I.sellerLaw j) (atoms (I.sellerLaw j))
      (alphaVirtualCost α (I.sellerLaw j)))
    (rank : Set (B × S) → ℕ) (hrank : IsTieOrder I rank) :
    (∀ T : B × S → ℕ → ℕ → ℝ, IsB11Table α I T →
      ((marketTarget I rank T : ℝ) : EReal) ≤ ValphaOn I (suppDomain I) α) ∧
    ∑ᶠ e ∈ posEdges I, betaE α I e * FBe I rank e ≤ marketTarget I rank (envelopeTable α I) := by sorry

end BilatMatch.Supplement
