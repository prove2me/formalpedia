-- Prove2me | Theorems.Thm_ExactAutobid_Equilibria_lemma_A_1
-- name    : ExactAutobid.Equilibria.lemma_A_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:57:24.130898+00:00
-- url     : https://prove2.me/theorems/f570945f-2f1a-4cf1-86bd-8428836fad52
-- title:
--   Lemma A.1 — ROI-GSP with a prescribed cap A > 1: existence, FIXP membership with polynomial support (uniform in A), polynomial time at A = 1
-- statement:
--   For every rational cap $A > 1$ and every ROI-constrained GSP auction, an equilibrium $(\alpha, \pi)$ with cap $A$ (Definition 2.3) exists; for every such $A$ there is a polynomial $p$ such that finding $\alpha$ together with an equilibrium distribution supported on at most $p(|\langle I\rangle|)$ legal orders is in FIXP; the same holds uniformly when $A > 1$ is part of the input; and at $A = 1$ an equilibrium, given as rational multipliers and a finite weighted list of legal orders, is computable in polynomial time:
--   $$\forall A > 1\;\forall I\;\exists (\alpha,\pi),\qquad \forall A>1\;\exists p\; \Pi^{\le p}_A \in \mathrm{FIXP},\qquad \exists p\; \Pi^{\le p}_{\mathrm{input}\,A} \in \mathrm{FIXP},\qquad \Pi_{1} \in \mathrm{FP}.$$
--
--   This supplies the membership half of Theorem 6.1 for prescribed caps.
--
--   Differences from the source:
--   - reading: GSP auctions (bidders with catalogs of positive values, CTRs, budgets) → the published Auction.ValidFor standing assumptions of [HLN26]: nonempty catalogs listed by nonincreasing positive value, 1 ≤ K ≤ M, CTRs in (0, 1] nonincreasing; positive budgets (budget model) or none (ROI model); reason: the paper takes its GSP model and FIXP membership from [HLN26]; the hard instances (K = M, unit CTRs) satisfy them
--   - reading: can be computed in FIXP with polynomial support over legal orders → ∃ polynomial p with InFIXP of the problem whose solutions α carry an equilibrium π supported on at most p(|enc I|) orders; reason: the support bound is part of what the FIXP computation outputs
--   - reading: circuit size and constant bit lengths polynomial in the auction encoding length and the binary length of A, including when A is an input → ∃ p, InFIXP of the problem with instances (auction, rational A > 1) encoded as the auction followed by A in binary; reason: an SL reduction of polynomial time is exactly a circuit of polynomial size and bit lengths
--   - reading: at A = 1, an equilibrium is computable in polynomial time → a polynomial-time map (TM2ComputableInPolyTime) from encoded ROI auctions to a rational witness (α, weighted ranking list) representing an equilibrium with cap 1; reason: an equilibrium of the GSP model consists of α and a distribution over orders
--   - encoding: polynomial time (binary encoding length) → Mathlib's Turing.TM2ComputableInPolyTime on framed binary encodings over the four-letter alphabet Sym, as in the published FixpReciprocal_SLReduces; reason: Lean convention already fixed by the reused FIXP framework; every rational is written in binary
-- source:
--   Huang, Liu, Yan, On the Complexity of Exact Autobidding Equilibria, arXiv:2611.04475 (sha256 270d1b74…), p. 57 (PDF 59), Lemma A.1

import Mathlib
import Definitions.Def_FixpReciprocal_FIXPComplete
import Definitions.Def_AutobiddingGSP_Approximation_Model
import Definitions.Def_ExactAutobid_Equilibria_GSP

open FixpReciprocal AutobiddingGSP.Approximation

namespace ExactAutobid.Equilibria

/-- **Lemma A.1 (ROI-GSP membership with a prescribed cap).** For every rational cap `A > 1`,
ROI-GSP equilibria exist and can be computed in FIXP with polynomial support over legal orders;
this holds uniformly with the cap `A > 1` as an input. At `A = 1`, an equilibrium (rational
multipliers and a finite weighted list of legal orders) is computable in polynomial time. -/
theorem lemma_A_1 :
    (∀ A : ℚ, 1 < A → ∀ Au : Auction, ROIInstance Au →
      ∃ (α : Fin Au.n → ℝ) (π : Au.Alloc → ℝ), IsROIGSPEqCap Au (A : ℝ) α π) ∧
    (∀ A : ℚ, 1 < A → ∃ p : Polynomial ℕ, InFIXP (roiGSPCapSuppProblem A p)) ∧
    (∃ p : Polynomial ℕ, InFIXP (roiGSPInputCapSuppProblem p)) ∧
    ∃ F : {Au : Auction // ROIInstance Au} → List ℚ × List (ℚ × List (ℕ × ℕ)),
      Nonempty (Turing.TM2ComputableInPolyTime (fun I : {Au : Auction // ROIInstance Au} =>
        encGSP I.1) encGSPWitness F) ∧
      ∀ I, IsROIGSPCapWitness I.1 1 (F I) := by sorry

end ExactAutobid.Equilibria
