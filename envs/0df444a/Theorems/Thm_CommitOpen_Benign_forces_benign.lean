-- Prove2me | Theorems.Thm_CommitOpen_Benign_forces_benign
-- name    : CommitOpen.Benign.forces_benign
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T02:26:49.576721+00:00
-- url     : https://prove2.me/theorems/403f8d58-23e6-48b3-a623-cffa126add02
-- title:
--   §4.3, closing claim, p. 12 — after commit-and-open, Bob's state is negligibly close to one satisfying the benign bounds (1) for any β > 0
-- statement:
--   Fix the test fraction $0<\alpha<1$ and any $\beta>0$. There is a negligible function $\nu$ with the following property.
--
--   Let $m$ be the number of EPR pairs, $k=\lfloor\alpha m\rfloor$ the size of the test set and $n=m-k$. Let $\hat x\in\{0,1\}^m$ and $\hat\theta\in\{+,\times\}^m$ be the outcomes and bases Bob committed to, and let $|\varphi_{AE}\rangle$ be any unit vector of $\mathcal H_A\otimes\mathcal H_E$ (Alice's $m$ qubits and a finite-dimensional register of a dishonest Bob): the joint state right before Step 2 of the verification of Fig. 4. Then there is, for each test $(T,T')$, a unit vector $|\tilde\varphi^{test}_{AE}\rangle$ such that:
--
--   1. **(closeness)** the real state $\rho_{TestAE}=\sum_{test}P_{Test}(test)|test\rangle\langle test|\otimes|\varphi_{AE}\rangle\langle\varphi_{AE}|$ and the ideal state $\tilde\rho_{TestAE}=\sum_{test}P_{Test}(test)|test\rangle\langle test|\otimes|\tilde\varphi^{test}_{AE}\rangle\langle\tilde\varphi^{test}_{AE}|$ satisfy $\delta(\rho_{TestAE},\tilde\rho_{TestAE})\le\nu(m)$;
--   2. **(bounds (1))** running Steps 2 and 3 on the ideal state, every branch Alice accepts satisfies the bounds of Definition 4.1: for every test $(T,T')$, every choice $\theta$ of Alice's bases and every outcome $x$ with $x_i=\hat x_i$ for all $i\in T'$ whose part $x|_T$ has positive probability,
--   $$H_0(\rho_{ER})\le\beta n,$$
--   and for every $I\subseteq\bar T$ and every $x|_{\bar I}$ of positive probability,
--   $$H_\infty\big(X|_I\,\big|\,X|_{\bar I}=x|_{\bar I}\big)\ge d_H(\theta|_I,\hat\theta|_I)-\beta n.$$
--
--   This is the claim the paper's proof of Theorem 4.2 reduces to (p. 9): the dishonest Bob of the compiled protocol is $\beta$-benign for every $\beta>0$. Its computational wrapper (dual-mode commitments, the CRS model) is not part of this statement.
--
--   **Formalization Note.** $\nu$ depends on $\alpha$ and $\beta$ only, and is chosen before $m$, $\hat x$, $\hat\theta$, Bob's register and the state; the ideal vectors depend on the test only, not on $\theta$ or $x$. Closeness is stated before Steps 2–3 and the bounds on the ideal state after them, as in the paper's construction of $\rho_{Ideal}$ (p. 12); the trace distance does not increase under these steps, which is not restated. Rejecting branches carry no constraint ("either aborts, or else", Definition 4.1). Alice's measurement of $T$ in $\hat\theta|_T$ and of $\bar T$ in $\theta|_{\bar T}$ is one measurement in the mixed basis; the conditioning includes $x|_T$. $\rho_{ER}$ is Bob's (unnormalized) state given $x|_T$, which for a pure joint state is the pointwise purification of Definition 4.1. $|T|=\lfloor\alpha m\rfloor$ and $n=m-\lfloor\alpha m\rfloor$, equal to the paper's $\alpha m$ and $(1-\alpha)m$ when $\alpha m$ is an integer. The joint state is pure without loss of generality (p. 10).
-- source:
--   Damgård, Fehr, Lunemann, Salvail & Schaffner, Improving the Security of Quantum Protocols via Commit-and-Open, arXiv:0902.3918v4, p. 12, §4.3 (closing paragraph), with p. 9 and Definition 4.1, bounds (1), p. 7

import Mathlib
import Definitions.Def_CommitOpen_Benign_Model

namespace CommitOpen.Benign

theorem forces_benign (α β : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hβ : 0 < β) :
    ∃ ν : ℕ → ℝ, Negligible ν ∧
      ∀ (m : ℕ) (xhat θhat : Fin m → Bool) (E : Type) [Fintype E] [DecidableEq E]
        (φ : EuclideanSpace ℂ ((Fin m → Bool) × E)), ‖φ‖ = 1 →
        ∃ φt : Test m ⌊α * m⌋₊ → EuclideanSpace ℂ ((Fin m → Bool) × E),
          (∀ t, ‖φt t‖ = 1) ∧
          traceDistance (cqState (fun _ : Test m ⌊α * m⌋₊ => φ)) (cqState φt) ≤ ν m ∧
          ∀ (t : Test m ⌊α * m⌋₊) (θ x : Fin m → Bool),
            (∀ i ∈ t.1.2, x i = xhat i) →
            0 < ∑ y ∈ agreeOn t.1.1 x, outcomeProb (mixBasis t.1.1 θhat θ) (φt t) y →
            maxEntropy (bobState (mixBasis t.1.1 θhat θ) (φt t) t.1.1 x) ≤
                β * ((m - ⌊α * m⌋₊ : ℕ) : ℝ) ∧
              ∀ I : Finset (Fin m), I ⊆ t.1.1ᶜ →
                0 < ∑ y ∈ agreeOn Iᶜ x, outcomeProb (mixBasis t.1.1 θhat θ) (φt t) y →
                (hammingOn I θ θhat : ℝ) - β * ((m - ⌊α * m⌋₊ : ℕ) : ℝ) ≤
                  condMinEntropy (outcomeProb (mixBasis t.1.1 θhat θ) (φt t)) I x := by sorry

end CommitOpen.Benign
