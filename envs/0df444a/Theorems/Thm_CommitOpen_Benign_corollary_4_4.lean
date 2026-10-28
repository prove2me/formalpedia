-- Prove2me | Theorems.Thm_CommitOpen_Benign_corollary_4_4
-- name    : CommitOpen.Benign.corollary_4_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T02:26:40.840111+00:00
-- url     : https://prove2.me/theorems/6696a48a-bf73-4d94-a245-55e665bd42ca
-- title:
--   Corollary 4.4, p. 11 — min-entropy and max-entropy bounds h(err + ε)n after the test
-- statement:
--   Let $\varepsilon>0$, $\hat x\in\{0,1\}^m$, $\hat\theta\in\{+,\times\}^m$, and let $|\tilde\varphi^{test}_{AE}\rangle$ be a unit vector of the form of Lemma 4.3 for a fixed test $(T,T')$: $(\langle y|_{\hat\theta}\otimes1)|\tilde\varphi^{test}_{AE}\rangle=0$ for all $y\notin B_{test}$. Fix Alice's bases $\theta$ and an outcome $x|_T$ of measuring the registers $A_i$, $i\in T$, in the bases $\hat\theta_i$, observed with positive probability, and let
--   $$err:=r_H(x|_{T'},\hat x|_{T'}),\qquad err+\varepsilon\le\tfrac12.$$
--   Let $\sigma_E$ be Bob's state after this measurement, let $n=|\bar T|$, and let $X$ be the outcome of measuring the remaining registers in the bases $\theta|_{\bar T}$. Then
--   $$H_0(\sigma_E)\le h(err+\varepsilon)\,n,$$
--   and for every $I\subseteq\bar T$ and every $x|_{\bar I}$ of positive probability,
--   $$H_\infty\big(X|_I\,\big|\,X|_{\bar I}=x|_{\bar I}\big)\ge d_H(\theta|_I,\hat\theta|_I)-h(err+\varepsilon)\,n.$$
--
--   The number of errors on the checked positions bounds both the uncertainty of Alice's remaining bits and the size of Bob's quantum memory. With $err=0$ these are the bounds (1) of Definition 4.1 with $\beta=h(\varepsilon)$.
--
--   **Formalization Note.** The paper assumes $err\le\tfrac12$; the proof uses the Hamming-ball bound with radius $(err+\varepsilon)n$, valid only for $err+\varepsilon\le\tfrac12$. As printed the corollary fails ($err=\varepsilon=\tfrac12$: $B_{test}$ is everything, $H_0(\sigma_E)$ can be $n$, while $h(1)n=0$), so the hypothesis $err+\varepsilon\le\tfrac12$ is used. $|T|$ is any $k$ (the paper's $\alpha m$); the proof does not use it. Alice's measurements on $T$ (in $\hat\theta$) and on $\bar T$ (in $\theta$) are one measurement in the mixed basis; the conditioning $X|_{\bar I}=x|_{\bar I}$ includes the observed $x|_T$, as in the paper, where $|\psi_{AE}\rangle$ is the collapsed state. $\sigma_E$ is kept unnormalized (same rank). $I$ and $\bar I$ are sets of positions in $\{1,\dots,m\}$, with $I\subseteq\bar T$, as in footnote 12.
-- source:
--   Damgård, Fehr, Lunemann, Salvail & Schaffner, Improving the Security of Quantum Protocols via Commit-and-Open, arXiv:0902.3918v4, p. 11, Corollary 4.4 (with footnote 12)

import Mathlib
import Definitions.Def_CommitOpen_Benign_Model

namespace CommitOpen.Benign

theorem corollary_4_4 {m k : ℕ} {E : Type} [Fintype E] [DecidableEq E] (ε : ℝ) (hε : 0 < ε)
    (xhat θhat θ : Fin m → Bool) (t : Test m k)
    (φt : EuclideanSpace ℂ ((Fin m → Bool) × E)) (hunit : ‖φt‖ = 1)
    (hform : ∀ y, y ∉ goodSet ε xhat t → amp θhat y φt = 0)
    (x : Fin m → Bool) (herr : relHamming t.1.2 x xhat + ε ≤ 1 / 2)
    (hpos : 0 < ∑ y ∈ agreeOn t.1.1 x, outcomeProb (mixBasis t.1.1 θhat θ) φt y) :
    maxEntropy (bobState (mixBasis t.1.1 θhat θ) φt t.1.1 x) ≤
        binEntropy2 (relHamming t.1.2 x xhat + ε) * (t.1.1ᶜ.card : ℝ) ∧
      ∀ I : Finset (Fin m), I ⊆ t.1.1ᶜ →
        0 < ∑ y ∈ agreeOn Iᶜ x, outcomeProb (mixBasis t.1.1 θhat θ) φt y →
        (hammingOn I θ θhat : ℝ) - binEntropy2 (relHamming t.1.2 x xhat + ε) * (t.1.1ᶜ.card : ℝ) ≤
          condMinEntropy (outcomeProb (mixBasis t.1.1 θhat θ) φt) I x := by sorry

end CommitOpen.Benign
