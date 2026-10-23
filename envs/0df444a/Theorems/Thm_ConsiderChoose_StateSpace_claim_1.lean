-- Prove2me | Theorems.Thm_ConsiderChoose_StateSpace_claim_1
-- name    : ConsiderChoose.StateSpace.claim_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:30:59.806017+00:00
-- url     : https://prove2.me/theorems/adecda9a-3e2f-4c38-9d53-10ddf1f021b9
-- title:
--   Claim 1, p. 15 — if Φ(S₁,T₁) = Φ(S₂,T₂) and u′ ∈ T₂ \ T₁, then C_{u′} ∩ S₁ = ∅
-- statement:
--   Let $C_1,\dots,C_K\subseteq[N]$ be consideration sets over products numbered in the common preference order, and let $\mathcal S$ be the state space of the dynamic program of §3: the subproblems $(S,T)$ generated from the nontrivial connected components of $G[[N],[K]]$ by repeatedly stocking or skipping the most preferred remaining product $\min(S)$ and splitting the residual graph into its nontrivial components. Let $\Phi(S,T)=[\min(S)]\cap\bigcup_{u\in T}C_u$.
--
--   Suppose $(S_1,T_1),(S_2,T_2)\in\mathcal S$ satisfy $\Phi(S_1,T_1)=\Phi(S_2,T_2)$, and let $u'\in T_2\setminus T_1$. Then
--   $$C_{u'}\cap S_1=\emptyset.$$
--
--   In the paper this claim is the key step of the proof of Lemma 2 (injectivity of $\Phi$ on $\mathcal S$), which argues by contradiction from $T_2\setminus T_1\neq\emptyset$.
--
--   **Formalization Note.** The hypotheses are exactly those under which the paper states and proves the claim (Appendix EC.1.1). Because the claim sits inside a proof by contradiction, Lemma 2 shows that they can never all hold, so this statement is equivalent, given the rest of the paper's argument, to the key step of Lemma 2; it is not a statement about an inhabited situation.
-- source:
--   Aouad, Farias & Levi (2021), Management Science 67(6), accepted manuscript (LBS eprint 1426), p. 15, Claim 1 (proof of Lemma 2; proved in Appendix EC.1.1, p. ec1)

import Mathlib
import Definitions.Def_ConsiderChoose_StateSpace_Model

namespace ConsiderChoose.StateSpace

theorem claim_1 {N K : ℕ} (C : Fin K → Finset (Fin N))
    {S₁ S₂ : Finset (Fin N)} {T₁ T₂ : Finset (Fin K)}
    (h₁ : Reachable C S₁ T₁) (h₂ : Reachable C S₂ T₂) (hΦ : Phi C S₁ T₁ = Phi C S₂ T₂)
    {u' : Fin K} (hu : u' ∈ T₂ \ T₁) : C u' ∩ S₁ = ∅ := by sorry

end ConsiderChoose.StateSpace
