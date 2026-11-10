-- Prove2me | Theorems.Thm_BilatMatch_lemma_B_9
-- name    : BilatMatch.lemma_B_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:09:38.917471+00:00
-- url     : https://prove2.me/theorems/30bf4cdb-f3d5-4edf-87de-13e669db9958
-- title:
--   Lemma B.9 (Extension from Finite Submarkets and Convergence of First Best) — $\mathrm{FB}(\mathcal I_n)\uparrow\mathrm{FB}(\mathcal I)$, $V_\alpha(\mathcal I)\ge V_\alpha(\mathcal I_n)$
-- statement:
--   Let $\mathcal I$ be a market with countably many agents, any independent priors, downward-closed feasibility, and $\mathrm{FB}(\mathcal I)<\infty$. Choose increasing finite sets $B_n,S_n$ exhausting the agents, and let $\mathcal I_n$ keep their priors and the family $\mathcal F_n=\{M\in\mathcal F: M\subseteq B_n\times S_n\}$. Then:
--
--   1. $\mathrm{FB}(\mathcal I_n)\uparrow\mathrm{FB}(\mathcal I)$;
--   2. every admissible BIC/IIR mechanism on $\mathcal I_n$ extends to $\mathcal I$ by assigning zero allocation and payment to all other agents; the extension is an admissible BIC/IIR mechanism with the same expected gains and revenue, and hence preserves ex-ante weak budget balance;
--   3. in particular $V_\alpha(\mathcal I)\ge V_\alpha(\mathcal I_n)$ for every $\alpha\ge0$, and $\mathrm{SB}(\mathcal I)\ge\mathrm{SB}(\mathcal I_n)$.
--
--   **Formalization Note** $\mathcal I_n$ is a market on the subtypes of $B_n$ and $S_n$; the extension is described by its defining equations. Reports are whole-line in both markets.
--
--   Differences from the source:
--   - encoding: I_n retains the priors and the family F_n → a market on the subtypes B_n, S_n whose matchings are identified with their images in B × S; reason: same object
--   - reading: BIC/IIR for general priors → BIC and IIR at every real type and report in both markets; reason: the paper's mechanisms are built with whole-line BIC/IIR (eq. (1), Lemma B.4); for finite priors the support-restricted and whole-line values coincide (Lemma B.4(i)), so the hypothesis is unchanged and the conclusion takes the stronger reading
-- source:
--   Liu, Qin, Wang, From Bilateral Trade to Matching Markets: Sharp Gains from Trade, arXiv:2609.30702 (held version, sha256 ff1490ad…), Lemma B.9, p.36 (pdf p.38)

import Mathlib
import Definitions.Def_BilatMatch_submarket
import Definitions.Def_BilatMatch_ValphaOn
import Definitions.Def_BilatMatch_FB

open MeasureTheory

namespace BilatMatch

open Classical in
/-- **Lemma B.9 (Extension from Finite Submarkets and Convergence of First Best).** Liu, Qin, Wang,
arXiv:2609.30702 (held version, sha256 ff1490ad…), Lemma B.9, p.36 (pdf p.38).

Let `I` be a market with countably many agents, any independent priors, downward-closed feasibility
and `FB(I) < ∞`. Choose increasing finite sets `B_n`, `S_n` exhausting the agents, and let `I_n` keep
their priors and the family `F_n = {M ∈ F : M ⊆ B_n × S_n}`. Then `FB(I_n) ↑ FB(I)`; every admissible
BIC/IIR mechanism on `I_n` extends to `I` by assigning zero allocation and payment to all other
agents, and this extension is an admissible BIC/IIR mechanism with the same expected gains and
revenue (so it preserves ex-ante WBB); in particular `V_α(I) ≥ V_α(I_n)` (`α ≥ 0`) and
`SB(I) ≥ SB(I_n)`.

**Formalization Note** `I_n` is `I.restrict B_n S_n`, a market on the subtypes (its agents' profiles
are restrictions of profiles of `I`). The extension is given by its defining equations. Reports are
whole-line in both markets. "`FB(I_n) ↑ FB(I)`" is monotonicity and convergence in `ℝ≥0∞`. -/
theorem lemma_B_9 {B S : Type*} [Countable B] [Countable S] (I : Market B S) (hI : I.IsValid)
    (hfin : FB I < ⊤) (Bn : ℕ → Finset B) (Sn : ℕ → Finset S) (hBmono : Monotone Bn)
    (hSmono : Monotone Sn) (hBex : ∀ i, ∃ n, i ∈ Bn n) (hSex : ∀ j, ∃ n, j ∈ Sn n) :
    (Monotone (fun n => FB (I.restrict (Bn n : Set B) (Sn n : Set S))) ∧
      Filter.Tendsto (fun n => FB (I.restrict (Bn n : Set B) (Sn n : Set S))) Filter.atTop
        (nhds (FB I))) ∧
    (∀ n : ℕ, ∀ A : Mechanism (I.restrict (Bn n : Set B) (Sn n : Set S)), A.Admissible →
      A.IsBICOn (wholeLine _ _) → A.IsIIROn (wholeLine _ _) →
      ∃ A' : Mechanism I,
        (∀ θ ω, A'.alloc θ ω = Prod.map Subtype.val Subtype.val '' A.alloc (restrictProfile θ) ω) ∧
        (∀ θ i, A'.pay θ (Sum.inl i) =
          if h : i ∈ (Bn n : Set B) then A.pay (restrictProfile θ) (Sum.inl ⟨i, h⟩) else 0) ∧
        (∀ θ j, A'.pay θ (Sum.inr j) =
          if h : j ∈ (Sn n : Set S) then A.pay (restrictProfile θ) (Sum.inr ⟨j, h⟩) else 0) ∧
        A'.Admissible ∧ A'.IsBICOn (wholeLine B S) ∧ A'.IsIIROn (wholeLine B S) ∧
        A'.GFT = A.GFT ∧ A'.Rev = A.Rev ∧ (0 ≤ A.Rev → 0 ≤ A'.Rev)) ∧
    (∀ n : ℕ, (∀ α : ℝ, 0 ≤ α →
        Valpha (I.restrict (Bn n : Set B) (Sn n : Set S)) α ≤ Valpha I α) ∧
      SB (I.restrict (Bn n : Set B) (Sn n : Set S)) ≤ SB I) := by sorry

end BilatMatch
