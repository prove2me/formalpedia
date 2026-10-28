-- Prove2me | Theorems.Thm_CommitOpen_Benign_lemma_4_3
-- name    : CommitOpen.Benign.lemma_4_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T02:26:47.83712+00:00
-- url     : https://prove2.me/theorems/e7219245-03e6-427a-bd7b-512321030d4f
-- title:
--   Lemma 4.3, pp. 10–11 — ρ_TestAE is negligibly close to a state whose every branch is supported on B_test in Bob's basis
-- statement:
--   Fix $0<\alpha<1$ and $\varepsilon>0$. There is a negligible function $\nu$ with the following property. Let $m$ be the number of qubits, $k=\lfloor\alpha m\rfloor$, let $\hat x\in\{0,1\}^m$ and $\hat\theta\in\{+,\times\}^m$ be Bob's committed outcomes and bases, and let $|\varphi_{AE}\rangle$ be any unit vector of $\mathcal H_A\otimes\mathcal H_E$ (Alice's $m$ qubits and Bob's finite-dimensional register), the joint state right before Step 2 of the verification in Fig. 4. Then there are unit vectors $|\tilde\varphi^{test}_{AE}\rangle$, one for each test $(T,T')$, such that
--
--   1. each $|\tilde\varphi^{test}_{AE}\rangle$ has the form $\sum_{x\in B_{test}}\alpha^{test}_x|x\rangle_{\hat\theta}|\psi^x_E\rangle$, i.e. $(\langle x|_{\hat\theta}\otimes1)|\tilde\varphi^{test}_{AE}\rangle=0$ for every $x\notin B_{test}$;
--   2. the cq states $\rho_{TestAE}=\rho_{Test}\otimes|\varphi_{AE}\rangle\langle\varphi_{AE}|$ and $\tilde\rho_{TestAE}=\sum_{test}P_{Test}(test)|test\rangle\langle test|\otimes|\tilde\varphi^{test}_{AE}\rangle\langle\tilde\varphi^{test}_{AE}|$ satisfy
--   $$\delta(\rho_{TestAE},\tilde\rho_{TestAE})\le\nu(m).$$
--
--   Up to a negligible error, for every choice of the test and every outcome on $T$, the error rate observed on $T'$ bounds the error rate Alice would see on $\bar T$ if she measured in Bob's bases.
--
--   **Formalization Note.** "Negligibly close (in $m$)" is read as one negligible $\nu$, chosen before $m$, $\hat x$, $\hat\theta$, Bob's register and the state, so uniform in all of them. The coefficients $\alpha^{test}_x$ are arbitrary, so the form in item 1 is exactly vanishing amplitude outside $B_{test}$. The state is pure; the paper notes (p. 10) that a mixed state is purified and the purifying register joins $E$. $|T|=\lfloor\alpha m\rfloor$.
-- source:
--   Damgård, Fehr, Lunemann, Salvail & Schaffner, Improving the Security of Quantum Protocols via Commit-and-Open, arXiv:0902.3918v4, pp. 10–11, Lemma 4.3

import Mathlib
import Definitions.Def_CommitOpen_Benign_Model

namespace CommitOpen.Benign

theorem lemma_4_3 (α ε : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hε : 0 < ε) :
    ∃ ν : ℕ → ℝ, Negligible ν ∧
      ∀ (m : ℕ) (xhat θhat : Fin m → Bool) (E : Type) [Fintype E] [DecidableEq E]
        (φ : EuclideanSpace ℂ ((Fin m → Bool) × E)), ‖φ‖ = 1 →
        ∃ φt : Test m ⌊α * m⌋₊ → EuclideanSpace ℂ ((Fin m → Bool) × E),
          (∀ t, ‖φt t‖ = 1) ∧
          (∀ t y, y ∉ goodSet ε xhat t → amp θhat y (φt t) = 0) ∧
          traceDistance (cqState (fun _ : Test m ⌊α * m⌋₊ => φ)) (cqState φt) ≤ ν m := by sorry

end CommitOpen.Benign
