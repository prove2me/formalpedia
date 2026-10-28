-- Prove2me | Theorems.Thm_CommitOpen_Benign_sampling_negligible
-- name    : CommitOpen.Benign.sampling_negligible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T02:26:48.682597+00:00
-- url     : https://prove2.me/theorems/540760e7-3949-448e-906e-76aea07dd1ff
-- title:
--   Proof of Lemma 4.3, p. 11 — for any outcome x, the probability over the test that x ∉ B_test is negligible in m
-- statement:
--   Fix $0<\alpha<1$ and $\varepsilon>0$. There is a negligible function $\nu$ such that for every $m$ and all strings $x,\hat x\in\{0,1\}^m$,
--   $$\Pr_{test\sim P_{Test}}\big[x\notin B_{test}\big]\le\nu(m),$$
--   where $test=(T,T')$, $T$ is a uniform subset of size $k=\lfloor\alpha m\rfloor$, $T'$ is a uniform subset of $T$, and
--   $B_{test}=\{x: r_H(x|_{\bar T},\hat x|_{\bar T})\le r_H(x|_{T'},\hat x|_{T'})+\varepsilon\}$.
--
--   The relative error rate on a random sample of positions predicts the error rate on the unsampled positions. This is the classical sampling problem the paper invokes with a reference to Hoeffding's inequality; it is the probabilistic core of Lemma 4.3.
--
--   **Formalization Note.** $\nu$ depends only on $\alpha$ and $\varepsilon$; it is uniform in $m$, $x$ and $\hat x$. The paper's $|T|=\alpha m$ is $\lfloor\alpha m\rfloor$, identical when $\alpha m$ is an integer. $r_H$ on $T'=\emptyset$ is $0$.
-- source:
--   Damgård, Fehr, Lunemann, Salvail & Schaffner, Improving the Security of Quantum Protocols via Commit-and-Open, arXiv:0902.3918v4, p. 11, proof of Lemma 4.3 (last sentence), citing [Hoe63]

import Mathlib
import Definitions.Def_CommitOpen_Benign_Model

namespace CommitOpen.Benign

theorem sampling_negligible (α ε : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hε : 0 < ε) :
    ∃ ν : ℕ → ℝ, Negligible ν ∧
      ∀ (m : ℕ) (x xhat : Fin m → Bool),
        ∑ t ∈ Finset.univ.filter (fun t : Test m ⌊α * m⌋₊ => x ∉ goodSet ε xhat t),
          testProb m ⌊α * m⌋₊ t ≤ ν m := by sorry

end CommitOpen.Benign
