-- Prove2me | Theorems.Thm_CodeSW_lemma_18
-- name    : CodeSW.lemma_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:27:26.90986+00:00
-- url     : https://prove2.me/theorems/4123d47a-dbe8-468c-a363-76f6b45fe4ce
-- title:
--   Lemma 18 — the two couplings of the even cover model to the random cluster model
-- statement:
--   **Coupling of even covers and the random cluster model.** Let $0<p<1$, and let $h^\perp$ be a column-generator matrix of $\mathrm{col}(h)^\perp$.
--
--   1. (Primal lift) Let $A\sim\xi_{h,p/2}$, and add each $e\in E\setminus A$ independently with probability $(p/2)/(1-p/2)$ to obtain $B$. Then $B\sim\phi_p$.
--   2. (Dual lift) Let $A\sim\xi_{h^\perp,(1-p)/(2-p)}$, and add each $e\in E\setminus A$ independently with probability $1-p$ to obtain $B$. Then $E\setminus B\sim\phi_p$.
--
--   Written out with $r=(p/2)/(1-p/2)$ and $r'=((1-p)/(2-p))/(1-(1-p)/(2-p))$, for every $B\subseteq E$:
--   $$\sum_{A\subseteq B}\xi_{h,p/2}(A)\,r^{|B\setminus A|}(1-r)^{|E\setminus B|}=\phi_p(B),$$
--   $$\sum_{A\subseteq E\setminus B}\xi_{h^\perp,(1-p)/(2-p)}(A)\,(1-p)^{|(E\setminus B)\setminus A|}p^{|B|}=\phi_p(B).$$
--
--   These couplings make samples of the even cover model into samples of the random cluster model, and they are what the flow of Theorem 16 lifts along.
--
--   Differences from the source:
--   - encoding: the law of B (primal) and of E ∖ B (dual) as outputs of a random procedure → the probability of each output written as an explicit finite sum; reason: the procedure is a finite product of independent choices
--   - encoding: ξ_{h^⊥,q} for a column generator h^⊥ of col(h)^⊥ → evenCover (col h) (q/(1−q)); reason: ker((h^⊥)ᵀ) = col(h) for every such generator
-- source:
--   Hangleiter, Ju, Vazirani, Code Swendsen-Wang Dynamics, arXiv:2510.08446 (manuscript sha256 4e4abb5e…), Lemma 18, p.20

import Definitions.Def_CodeSW_evenCover
import Definitions.Def_CodeSW_rc
open Matrix

namespace CodeSW

/-- **Lemma 18 (Coupling of even covers and RC).** For `0 < p < 1` there are two couplings of the
even-cover model to the random cluster model `ϕ_p`. Let `h^⊥` be a column-generator matrix of
`col(h)^⊥`.
1. (primal lift) Let `A ∼ ξ_{h,p/2}`, and add each `e ∈ E ∖ A` independently with probability
   `(p/2)/(1 − p/2)` to obtain `B`. Then `B ∼ ϕ_p`.
2. (dual lift) Let `A ∼ ξ_{h^⊥,(1−p)/(2−p)}`, and add each `e ∈ E ∖ A` independently with
   probability `1 − p` to obtain `B`. Then `E ∖ B ∼ ϕ_p`.
(Hangleiter, Ju, Vazirani, *Code Swendsen-Wang Dynamics*, arXiv:2510.08446, manuscript sha256
4e4abb5e…, Lemma 18, p.20.)

**Formalization Note** `ξ_{h,q}(A) ∝ (q/(1−q))^{|A|} 1(1_A ∈ ker hᵀ)` is
`evenCover (ker hᵀ) (q/(1−q))`, and `ξ_{h^⊥,q}` is `evenCover (col h) (q/(1−q))`
(`ker((h^⊥)ᵀ) = col(h)`). Each conclusion is the law of the output written out:
`Pr[B] = ∑_{A ⊆ B} ξ(A) r^{|B∖A|} (1−r)^{|E∖B|}` with `r` the addition probability, and in the dual
case `Pr[E∖B = B₀] = Pr[B = E∖B₀]`. -/
theorem lemma_18 {c n : ℕ} (h : Matrix (Fin c) (Fin n) (ZMod 2)) (p : ℝ) (hp0 : 0 < p)
    (hp1 : p < 1) :
    (∀ B : Finset (Fin c),
      ∑ A ∈ B.powerset,
        evenCover (LinearMap.ker hᵀ.mulVecLin) ((p / 2) / (1 - p / 2)) A *
          ((p / 2) / (1 - p / 2)) ^ (B \ A).card *
          (1 - (p / 2) / (1 - p / 2)) ^ (Finset.univ \ B).card = rc h p B) ∧
    (∀ B : Finset (Fin c),
      ∑ A ∈ (Finset.univ \ B).powerset,
        evenCover (LinearMap.range h.mulVecLin)
            (((1 - p) / (2 - p)) / (1 - (1 - p) / (2 - p))) A *
          (1 - p) ^ ((Finset.univ \ B) \ A).card * (1 - (1 - p)) ^ B.card = rc h p B) := by sorry

end CodeSW
