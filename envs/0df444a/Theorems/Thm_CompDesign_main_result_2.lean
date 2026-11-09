-- Prove2me | Theorems.Thm_CompDesign_main_result_2
-- name    : CompDesign.main_result_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:59:50.79149+00:00
-- url     : https://prove2.me/theorems/f6b35929-edfe-4a00-9446-878f11a2a6f2
-- title:
--   Main Result 2 — strict better responses of $\Gamma^{mc}$ terminate at pure Nash equilibria, each with $\mathrm{OPT}\le(1+\kappa(\lambda))v(S)\le\frac{2-\lambda}{1-\lambda}v(S)$
-- statement:
--   Throughout, $N=\{1,\dots,n\}$ is the set of agents, $B>0$ the budget, $c_i\ge 0$ the private costs, and $v:2^N\to\mathbb R$ a value function satisfying Assumption 3.1: $v(\emptyset)=0$, $v$ monotone ($S\subseteq S'\Rightarrow v(S)\le v(S')$) and submodular ($v(S\cup\{i\})-v(S)\ge v(S'\cup\{i\})-v(S')$ whenever $S\subseteq S'$ and $i\notin S'$). The marginal-contribution payment is $p^{mc}_i(S)=B\,\frac{v(S)-v(S\setminus\{i\})}{v(S)}$ if $i\in S$ and $v(S)>0$, and $0$ otherwise (8); agent $i$'s utility is $u_i(S)=p^{mc}_i(S)-c_i$ if $i\in S$ and $0$ otherwise.
--
--   Let $\mathrm{OPT}=\max\{v(T):T\subseteq N,\ \sum_{i\in T}c_i\le B\}$ (4) and let $\kappa$ be the cost concentration term (20).
--
--   **Main Result 2**, in the precise form of Theorems 4.1 and 5.1. Let $\lambda=\max_i c_i/B<1$. For any monotone submodular value function, in the game $\Gamma^{mc}$ induced by the marginal contribution rule:
--
--   1. every sequence of strict better responses terminates (no infinite sequence $S_0,S_1,\dots$ in which each $S_{t+1}$ is a strict better response from $S_t$);
--   2. $\Gamma^{mc}$ has a pure Nash equilibrium;
--   3. every pure Nash equilibrium $S$ satisfies $\mathrm{OPT}\le(1+\kappa(\lambda))\,v(S)$;
--   4. $1+\kappa(\lambda)\le\dfrac{2-\lambda}{1-\lambda}$.
--
--   In particular every pure Nash equilibrium satisfies $\mathrm{OPT}/v(S)\le(2-\lambda)/(1-\lambda)=2+o_\lambda(1)$: the principal secures a constant fraction of the full-information optimum without knowing any cost.
--
--   **Formalization Note** `λ` is written `l` and enters as any $l$ with $0\le l<1$ and $c_i\le lB$ for all $i$. A ratio bound $\mathrm{OPT}/v(S)\le\rho$ is written $\mathrm{OPT}\le\rho\,v(S)$.
--
--   Differences from the source:
--   - generalization: Main Result 2 as printed: a pure Nash equilibrium exists, and OPT/v(S) ≤ (2−λ)/(1−λ) for every one → adds termination of every strict better-response sequence and the sharper constant 1 + κ(λ); reason: these are the clauses of Theorems 4.1 and 5.1, which the paper gives as the precise versions of Main Result 2; the printed claim follows from clauses 2–4
--   - encoding: λ = max_i c_i/B → any l with 0 ≤ l < 1 and c_i ≤ l·B for every i; reason: the paper's λ is the least such l and κ(l) and (2−l)/(1−l) are nondecreasing in l, so the case l = max_i c_i/B is the paper's statement; for n = 0 the max is undefined and the claim is trivial
--   - encoding: κ(λ) = max over finite families (20) → kappa l = sSup over families x : Fin m → ℝ, every m; reason: for 0 ≤ l < 1 the set is nonempty and bounded above, so sSup is its supremum, which Claim 5.1 shows is attained
--   - encoding: PoA_PNE ≤ ρ, a supremum of ratios OPT/v(S) with +∞ when OPT > 0 = v(S) (5) → OPT ≤ ρ · v(S) for every pure Nash equilibrium S; reason: equivalent to the ratio bound for every instance, including the +∞ convention, and avoids division
--   - encoding: OPT/v(S) ≤ (2 − λ)/(1 − λ) = 2 + o_λ(1) → OPT ≤ (1 + κ(l)) v(S) and 1 + κ(l) ≤ (2 − l)/(1 − l), no asymptotic clause; reason: the ratio bound and the limit 2 as λ → 0 follow from the two explicit inequalities
--   - encoding: every sequence of strict better responses terminates → there is no f : ℕ → Finset (Fin n) with a strict better response from f t to f (t+1) for every t; reason: a sequence terminates iff it is not infinite; this is the standard well-foundedness formulation
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), §1.2.1, Main Result 2, p.5 (PDF 8); precise versions Theorem 4.1, p.17 (PDF 20) and Theorem 5.1, p.27 (PDF 30)

import Mathlib
import Definitions.Def_CompDesignBFM_IsMonotoneSF
import Definitions.Def_CompDesignBFM_IsSubmodularSF
import Definitions.Def_CompDesignBFM_IsPNE
import Definitions.Def_CompDesignBFM_OPT
import Definitions.Def_CompDesign_IsStrictImprovement
import Definitions.Def_CompDesign_kappa

open CompDesignBFM

namespace CompDesign

/-- Main Result 2, §1.2.1, p.5 (PDF 8) of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), in the precise form of Theorem 4.1 (p.17) and
Theorem 5.1 (p.27). Let `λ = max_i c_i/B < 1`. For any monotone submodular value function, in the game
induced by the marginal contribution rule every sequence of strict better responses terminates, a pure
Nash equilibrium exists, and every pure Nash equilibrium `S` satisfies
`OPT ≤ (1 + κ(λ)) v(S)` with `1 + κ(λ) ≤ (2 − λ)/(1 − λ)`; so `OPT/v(S) ≤ (2 − λ)/(1 − λ) = 2 + o_λ(1)`.

**Formalization Note.** `λ` is written `l` and enters as any `l` with `0 ≤ l < 1` and `c_i ≤ l B` for
all `i`; the paper's `λ = max_i c_i/B` is the least such `l`. A price-of-anarchy bound `ρ` is written
`OPT ≤ ρ v(S)` for every pure Nash equilibrium `S`, with no ratio. Termination is the absence of an
infinite strict-better-response sequence. Assumption 3.1, `B > 0` and `c ≥ 0` are the standing
assumptions of §3.1. -/
theorem main_result_2 {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (c : Fin n → ℝ) (hB : 0 < B)
    (hv0 : v ∅ = 0) (hm : IsMonotoneSF v) (hs : IsSubmodularSF v) (hc : ∀ i, 0 ≤ c i)
    (l : ℝ) (hl0 : 0 ≤ l) (hl1 : l < 1) (hcl : ∀ i, c i ≤ l * B) :
    (¬ ∃ f : ℕ → Finset (Fin n), ∀ t, IsStrictImprovement v B c (f t) (f (t + 1))) ∧
    (∃ S : Finset (Fin n), IsPNE v B c S) ∧
    (∀ S : Finset (Fin n), IsPNE v B c S → OPT v B c ≤ (1 + kappa l) * v S) ∧
    1 + kappa l ≤ (2 - l) / (1 - l) := by sorry

end CompDesign
