-- Prove2me | Theorems.Thm_CompDesign_theorem_5_1
-- name    : CompDesign.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:56:37.813729+00:00
-- url     : https://prove2.me/theorems/98456909-bc7c-4083-8f52-7fd5f64675f4
-- title:
--   Theorem 5.1 — $\mathrm{PoA}_{\mathrm{PNE}}\le 1+\kappa(\lambda)\le(2-\lambda)/(1-\lambda)$
-- statement:
--   Throughout, $N=\{1,\dots,n\}$ is the set of agents, $B>0$ the budget, $c_i\ge 0$ the private costs, and $v:2^N\to\mathbb R$ a value function satisfying Assumption 3.1: $v(\emptyset)=0$, $v$ monotone ($S\subseteq S'\Rightarrow v(S)\le v(S')$) and submodular ($v(S\cup\{i\})-v(S)\ge v(S'\cup\{i\})-v(S')$ whenever $S\subseteq S'$ and $i\notin S'$). The marginal-contribution payment is $p^{mc}_i(S)=B\,\frac{v(S)-v(S\setminus\{i\})}{v(S)}$ if $i\in S$ and $v(S)>0$, and $0$ otherwise (8); agent $i$'s utility is $u_i(S)=p^{mc}_i(S)-c_i$ if $i\in S$ and $0$ otherwise.
--
--   Let $\mathrm{OPT}=\max\{v(T):T\subseteq N,\ \sum_{i\in T}c_i\le B\}$ (4) and let $\kappa$ be the cost concentration term (20).
--
--   **Theorem 5.1 (Pure Nash equilibrium PoA bound).** Let $\lambda=\max_{i\in N}c_i/B<1$. The game $\Gamma^{mc}$ induced by the marginal contribution payment rule (8) satisfies
--   $$\mathrm{PoA}_{\mathrm{PNE}}\le 1+\kappa(\lambda)\le\frac{2-\lambda}{1-\lambda}.$$
--   Explicitly:
--
--   1. every pure Nash equilibrium $S$ of $\Gamma^{mc}$ satisfies $\mathrm{OPT}\le(1+\kappa(\lambda))\,v(S)$;
--   2. $1+\kappa(\lambda)\le(2-\lambda)/(1-\lambda)$.
--
--   In particular, as $\lambda\to 0$, every pure Nash equilibrium attains value at least $(1/2-o(1))\,\mathrm{OPT}$. This is the price-of-anarchy half of Main Result 2: a cost-oblivious rule guarantees about half of the full-information optimum.
--
--   **Formalization Note** `λ` is written `l` and enters as any $l$ with $0\le l<1$ and $c_i\le lB$ for all $i$. A price-of-anarchy bound $\rho$ is written as $\mathrm{OPT}\le\rho\,v(S)$ for every pure Nash equilibrium $S$.
--
--   Differences from the source:
--   - encoding: λ = max_i c_i/B → any l with 0 ≤ l < 1 and c_i ≤ l·B for every i; reason: the paper's λ is the least such l and κ(l) and (2−l)/(1−l) are nondecreasing in l, so the case l = max_i c_i/B is the paper's statement; for n = 0 the max is undefined and the claim is trivial
--   - reading: Theorem 5.1 prints only λ = max_i c_i/B → hypothesis l < 1; reason: the bound (2−λ)/(1−λ) is undefined at λ = 1 and negative beyond, κ(λ) is infinite for λ ≥ 1, the proof uses c_i < B, and Main Result 2, which Theorem 5.1 makes precise, assumes λ < 1
--   - encoding: κ(λ) = max over finite families (20) → kappa l = sSup over families x : Fin m → ℝ, every m; reason: for 0 ≤ l < 1 the set is nonempty and bounded above, so sSup is its supremum, which Claim 5.1 shows is attained
--   - encoding: PoA_PNE ≤ ρ, a supremum of ratios OPT/v(S) with +∞ when OPT > 0 = v(S) (5) → OPT ≤ ρ · v(S) for every pure Nash equilibrium S; reason: equivalent to the ratio bound for every instance, including the +∞ convention, and avoids division
--   - encoding: "in particular, as λ → 0, every pure Nash equilibrium attains value at least (1/2 − o(1))OPT" → no separate clause; reason: it follows from the explicit clauses OPT ≤ (1+κ(l))v(S) ≤ ((2−l)/(1−l))v(S), since (1−l)/(2−l) → 1/2
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), §5.1, Theorem 5.1, p.27 (PDF 30)

import Mathlib
import Definitions.Def_CompDesignBFM_IsMonotoneSF
import Definitions.Def_CompDesignBFM_IsSubmodularSF
import Definitions.Def_CompDesignBFM_IsPNE
import Definitions.Def_CompDesignBFM_OPT
import Definitions.Def_CompDesign_kappa

open CompDesignBFM

namespace CompDesign

/-- Theorem 5.1 (Pure Nash equilibrium PoA bound), §5.1, p.27 (PDF 30) of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…).
Let `λ = max_{i∈N} c_i/B`. The game `Γ^mc` induced by the marginal contribution payment rule (8)
satisfies `PoA_PNE ≤ 1 + κ(λ) ≤ (2 − λ)/(1 − λ)`.

**Formalization Note.** `λ` is written `l` and enters as any `l` with `0 ≤ l < 1` and `c_i ≤ l B` for
all `i`; the paper's `λ = max_i c_i/B` is the least such `l`, and `κ` is monotone in `l`. `λ < 1` is
the regime of Main Result 2, without which the right-hand side is undefined. `PoA_PNE ≤ ρ` is written as
`OPT ≤ ρ v(S)` for every pure Nash equilibrium `S`, which is (5) without the ratio. The sentence "as
`λ → 0`, every pure Nash equilibrium attains value at least `(1/2 − o(1)) OPT`" follows from the two
explicit clauses. Assumption 3.1, `B > 0` and `c ≥ 0` are the standing assumptions of §3.1. -/
theorem theorem_5_1 {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (c : Fin n → ℝ) (hB : 0 < B)
    (hv0 : v ∅ = 0) (hm : IsMonotoneSF v) (hs : IsSubmodularSF v) (hc : ∀ i, 0 ≤ c i)
    (l : ℝ) (hl0 : 0 ≤ l) (hl1 : l < 1) (hcl : ∀ i, c i ≤ l * B) :
    (∀ S : Finset (Fin n), IsPNE v B c S → OPT v B c ≤ (1 + kappa l) * v S) ∧
    1 + kappa l ≤ (2 - l) / (1 - l) := by sorry

end CompDesign
