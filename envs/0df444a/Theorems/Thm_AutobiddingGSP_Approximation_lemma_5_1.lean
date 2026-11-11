-- Prove2me | Theorems.Thm_AutobiddingGSP_Approximation_lemma_5_1
-- name    : AutobiddingGSP.Approximation.lemma_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:29:41.676236+00:00
-- url     : https://prove2.me/theorems/39f66f26-0c07-4cf7-b314-bb54f54831d2
-- title:
--   Lemma 5.1 — the budget circuit is polynomial-time constructible and its fixed points are γ-approximate ABE-B
-- statement:
--   For every auction satisfying the budget-model assumptions and every rational $0<\gamma<1$: (1) there is a polynomial-time computable map sending the code of $(A,\gamma)$ to the code of the circuit of §§4, 5.2 (with its output nodes); (2) at every fixed point of that circuit, the multipliers and the randomized allocation read off $(w_h,\mathrm{ItemIdx}_h)_{h\in[Q]}$ form a γ-approximate ABE-B (bid-consistent support, $P_i\le B_i$, and $P_i<(1-\gamma)B_i\Rightarrow\alpha_i=1$).
--
--   Differences from the source:
--   - encoding: Heaviside, y·H(x) and w·D_ℵ pseudogates implemented by PL gadgets with auxiliary variables ([FRHHH24, Lemma 3.1, Prop. 3.3]) → primitive correspondence gates; a fixed point satisfies every gate relation; reason: the paper specifies each pseudogate by this relation at fixed points
--   - reading: a sorting network, i.e., AKS → an insertion network of comparators; reason: every sorting network outputs the sorted values; only the size differs and it stays polynomial
--   - encoding: binary addition and constant-multiplication gates → one rational linear-combination gate per sum; ∑_ℓ p_{h,t,ℓ} as one gate per group; reason: composites of the paper's gates; same values
--   - reading: each payment summand by two successive applications of y·H(x) → the first application is the node b_s H(½ − |Idx_{h,s} − N_{h,t}|) already used in J_{h,t}; reason: the paper does not say whether the two uses share a node
--   - reading: Without loss of generality, suppose T ≥ 2 → T ≥ 2 as in the paper; for T = 1 the branch E = (0, 1), Q = 1, Idx = 0; reason: the paper's formulas need T ≥ 2 and it omits the trivial case
--   - encoding: γ of polynomial bit size; the circuit constructed in polynomial time → γ rational in binary after the auction; a Cook-machine polynomial-time map from that input to the circuit's code with its output nodes; reason: the instance determines the circuit; this is polynomial time in the input
--   - encoding: (α, π) at the fixed point, π = (w_h, ItemIdx_h) → α = the multiplier nodes; π(a) = ∑_h w_h [ItemIdx_h is the rank vector of a]; reason: the paper's reading of the circuit's outputs
-- source:
--   Hansen, Li and Nie (2026), Complexity of Autobidding Equilibria in GSP Sponsored Shopping, arXiv:2610.13716 [arXiv version unverified; supplied PDF revision created 2026-11-03, SHA256 40ce53fb39e7897580c44ffab04f7611388d8afc4c26ee7118de76bd21b73c8f], Lemma 5.1, p. 23 (PDF 23); circuit §§4.1–4.2, 5.1–5.2, pp. 12–23

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_QAlgorithms_ClassicalRationalEncoding
import Definitions.Def_AutobiddingGSP_Approximation_Model
import Definitions.Def_AutobiddingGSP_Approximation_Search
import Definitions.Def_AutobiddingGSP_Approximation_PLCircuit
import Definitions.Def_AutobiddingGSP_Approximation_MembershipCircuit

namespace AutobiddingGSP.Approximation

/-- **Lemma 5.1** (Hansen, Li and Nie, *Complexity of Autobidding Equilibria in GSP Sponsored Shopping*, arXiv:2610.13716 [arXiv version unverified; supplied PDF SHA256 40ce53fb…c73c8f], p. 23 (PDF 23); circuit of §4 and §5.2, pp. 22–23). When `0 < γ < 1` has polynomial bit size, the circuit can be constructed in polynomial
time. Moreover, when the circuit is at a fixed point, `(α, π)` is a γ-approximate equilibrium for
ABE-B.

Both clauses: (1) a polynomial-time machine maps the code of every instance (auction and rational
`0 < γ < 1`, in binary) to the code of the circuit `memCircuit A Model.budget γ` with its designated
outputs; (2) at every fixed point `v` of that circuit, the multipliers `α = (v_0, …, v_{n−1})` and
the randomized allocation `π = ∑_h w_h δ_{σ_h}` read off `(w_h, ItemIdx_h)_{h ∈ [Q]}` form a
γ-approximate ABE-B, including exact feasibility. -/
theorem lemma_5_1 :
    (∃ f : List Bool → List Bool, CookPvsNP.PolyTimeComputable f ∧
      ∀ (A : Auction) (γ : ℚ), A.ValidFor Model.budget false → 0 < γ → γ < 1 →
        f (encAuction A ++ QAlgorithms.LocalHamiltonian.encRat γ) =
          encMemCircuit (memCircuit A Model.budget γ)) ∧
    ∀ (A : Auction) (γ : ℚ), A.ValidFor Model.budget false → 0 < γ → γ < 1 →
      ∀ v : ℕ → ℝ, IsFixedPoint (memCircuit A Model.budget γ).gates v →
        A.IsApproxABEB γ (decodeAlpha A v) (decodePi A (memCircuit A Model.budget γ) v) := by sorry

end AutobiddingGSP.Approximation
