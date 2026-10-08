-- Prove2me | Theorems.Thm_BNCovPack_SetCover_lemma_5_1_i
-- name    : BNCovPack.SetCover.lemma_5_1_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T02:06:01.339449+00:00
-- url     : https://prove2.me/theorems/28e65b42-8b25-4ea7-a381-6decbb873be1
-- title:
--   Lemma 5.1 (i) — initially $\Phi\le 1$, and $\Phi>0$ at all times
-- statement:
--   Let $X$ be a ground set of $n$ elements, $\mathcal S$ a finite family of sets, and $OPT\ge 1$ a natural number. Let $\Phi=\Phi_1+\Phi_2$ be the potential of Section 5.1, with $r=e\ln(e/(e-1))$ and $\alpha=\max\{1,\ln(rn/OPT)\}$. Then:
--
--   1. at start, when every weight is $0$ and no set is chosen,
--   $$\Phi(0,\emptyset)=1-(1-e^{-\alpha})^n+e^{-OPT}\le 1;$$
--   2. for every real $\alpha$, every weight vector $w$ and every family $\mathcal C$ of sets, $\Phi(w,\mathcal C)>0$.
--
--   Together with Lemma 5.1 (ii), part 1 gives $\Phi\le 1$ throughout the run of the algorithm, which is what Lemma 5.2 uses; part 2 is the positivity used to conclude that each term of $\Phi$ is at most $1$.
--
--   **Formalization Note** The page's proof writes "$1-\exp(-dne^{-\alpha})$" and "$\alpha\ge\ln(dn/OPT)$"; the letter $d$ there is a misprint for $r$, since the chosen $\alpha$ only gives $rne^{-\alpha}\le OPT$, and $1-x\ge e^{-rx}$ holds for $0\le x\le 1/e$ with this $r$. The statement uses $r$. Positivity is stated for all states, not only those reached by the algorithm. $n=0$ is allowed (then $\Phi(0,\emptyset)=e^{-OPT}$).
-- source:
--   Buchbinder, Naor, Online Primal-Dual Algorithms for Covering and Packing, Math. Oper. Res. (2009), DOI 10.1287/moor.1080.0363, p. 12, Lemma 5.1 (i); proof p. 13 (α, r, initial value of Φ)

import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance
import Definitions.Def_BNCovPack_SetCover_Potential

namespace BNCovPack.SetCover

open OnlinePrimalDual.OnlineSetCover

/-- **Lemma 5.1 (i)** (Buchbinder–Naor 2009, p. 12; proof p. 13): at start (all weights `0`,
empty cover) `Φ ≤ 1` when `α = max {1, ln(r n / OPT)}`, `r = e ln(e/(e−1))`, `n = |E|`, and
`OPT ≥ 1`; and `Φ > 0` in every state (every weight vector `w`, every family `C`, every `α`). -/
theorem lemma_5_1_i {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (OPT : ℕ) (hOPT : 1 ≤ OPT) :
    potential inst (alphaParam (Fintype.card E) OPT) OPT (fun _ => 0) ∅ ≤ 1 ∧
    ∀ (α : ℝ) (w : T → ℝ) (C : Finset T), 0 < potential inst α OPT w C := by sorry

end BNCovPack.SetCover
