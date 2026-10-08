-- Prove2me | Theorems.Thm_BNCovPack_SetCover_lemma_5_2
-- name    : BNCovPack.SetCover.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T02:29:57.896223+00:00
-- url     : https://prove2.me/theorems/70db386b-0529-42e5-b5f7-3f76d91f960f
-- title:
--   Lemma 5.2 — the online algorithm covers every arriving element and chooses at most $(2\alpha\ln(1+d)+1)\,OPT/\ln 2$ sets
-- statement:
--   Consider online unweighted set cover: a ground set $X$ of $n$ elements, a finite family $\mathcal S$ of sets, all of cost $1$, and $d\ge1$ an upper bound on the frequency of every element (the number of sets containing it). Elements arrive in a list $\sigma$. Let $OPT\ge 1$ be a natural number such that some family of at most $OPT$ sets covers every element of $\sigma$. Run the algorithm of Section 5.1 with any $B>0$, any order of the sets, frequency parameter $d$ and the value $OPT$, and let $\mathcal C$ be the family it has chosen. Then:
--
--   1. every element of $\sigma$ is covered by a set of $\mathcal C$;
--   2. with $r=e\ln(e/(e-1))$ and $\alpha=\max\{1,\ln(rn/OPT)\}$,
--   $$|\mathcal C|\ \le\ \frac{\big(2\alpha\ln(1+d)+1\big)\,OPT}{\ln 2}.$$
--
--   Since $\alpha=O(\log(n/OPT))$, this is the paper's guarantee that the deterministic online algorithm is $O(\log d\log(n/OPT))$-competitive for online unweighted set cover, improving the $O(\log m\log n)$ of Alon et al. Because $\sigma$ is arbitrary, both claims hold at every time of the run.
--
--   **Formalization Note** The paper writes $OPT\cdot O(\log d\log(n/OPT))$; the proof yields $(2\alpha\ln(1+d)+1)\,OPT/\ln 2$, from $\sum_s\chi_{\mathcal C}(s)\le\frac{1}{\ln 2}\alpha\sum_s w(s)+\frac{1}{\ln2}OPT$ and the fractional bound $\sum_s w(s)\le 2\ln(1+d)\,OPT$. The paper assumes $OPT$ is known and equal to the optimum; here $OPT$ is any known upper bound on the optimum (at the optimum this is the paper's statement). $d$ may be any upper bound on the maximum frequency (at the maximum frequency this is the paper's statement). Unit costs are the hypothesis $c\equiv1$ on the published instance type. The doubling wrapper for unknown $OPT$ is not part of the statement.
-- source:
--   Buchbinder, Naor, Online Primal-Dual Algorithms for Covering and Packing, Math. Oper. Res. (2009), DOI 10.1287/moor.1080.0363, p. 14, Lemma 5.2 and its proof; model p. 12, Section 5.1

import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_coveredBy
import Definitions.Def_BNCovPack_SetCover_Potential
import Definitions.Def_BNCovPack_SetCover_Algorithm

namespace BNCovPack.SetCover

open OnlinePrimalDual.OnlineSetCover

/-- **Lemma 5.2** (Buchbinder–Naor 2009, p. 14): the online unweighted set-cover algorithm of §5.1
(unit costs, fractional scheme with `ℓ = d`, rounding by the potential `Φ` with
`α = max {1, ln(r n/OPT)}`), run with any `B > 0`, any processing order of the sets, and a known
value `OPT ≥ 1` such that some family of at most `OPT` sets covers every arriving element,
(i) covers every element that is given to it, and
(ii) chooses at most `(2 α ln(1 + d) + 1) · OPT / ln 2` sets.
The paper writes `OPT · O(log d log(n/OPT))`; the proof yields `(2α ln(1+d) + 1)·OPT/ln 2`. -/
theorem lemma_5_2 {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (hc : ∀ s, inst.c s = 1)
    (B : ℝ) (hB : 0 < B) (d : ℕ) (hd : 1 ≤ d) (hfreq : ∀ e, (inst.elemSets e).card ≤ d)
    (OPT : ℕ) (hOPT : 1 ≤ OPT) (ord : List T) (hord : ∀ s, s ∈ ord) (σ : List E)
    (hopt : ∃ F : Finset T, F.card ≤ OPT ∧ ∀ e ∈ σ, coveredBy inst F e) :
    (∀ e ∈ σ, coveredBy inst (run inst B d OPT ord σ).cover e) ∧
    ((run inst B d OPT ord σ).cover.card : ℝ)
      ≤ (2 * alphaParam (Fintype.card E) OPT * Real.log (1 + (d : ℝ)) + 1) * (OPT : ℝ)
          / Real.log 2 := by sorry

end BNCovPack.SetCover
