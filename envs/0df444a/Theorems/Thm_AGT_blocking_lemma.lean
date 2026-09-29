-- Prove2me | Theorems.Thm_AGT_blocking_lemma
-- name    : AGT.blocking_lemma
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-13T10:47:52.875683+00:00
-- url     : https://prove2.me/theorems/04e9556b-f524-410e-b551-1ca155d20bb3
-- title:
--   The Blocking Lemma (Gale--Sotomayor)
-- statement:
--   **The Blocking Lemma of Gale and Sotomayor.** Fix a two-sided market with a finite set $M$ of men and a finite set $W$ of women, each agent holding a strict ordering of the opposite side, and let matchings be bijections $M \to W$.
--
--   Let $\mu$ be a *male-optimal* stable matching: it is stable, and every man weakly prefers it to his partner in any other stable matching. Let $\nu$ be an arbitrary matching — no stability is assumed of it — and put
--   $$R \;=\; \{\, m \in M \;:\; \nu(m) \succ_m \mu(m) \,\},$$
--   the set of men who strictly prefer $\nu$ to the male-optimal stable matching. Assume $R \neq \emptyset$, witnessed by a man $m_0$.
--
--   The lemma asserts that $\nu$ is then blocked by a pair drawn from outside $R$ on the man's side and from inside $\nu(R)$ on the woman's side: there exist men $m$ and $m'$ with $m' \in R$ and $m \notin R$ such that the pair $(m, \nu(m'))$ blocks $\nu$, i.e.
--   $$\nu(m') \succ_m \nu(m) \qquad\text{and}\qquad m \succ_{\nu(m')} \nu^{-1}(\nu(m')) = m'.$$
--
--   The point of the statement is the location of the blocking pair. That an unstable $\nu$ has *some* blocking pair is immediate from male-optimality once some man prefers $\nu$; what the lemma adds is that one can always find a blocking man who does **not** belong to $R$, paired with a woman who is matched under $\nu$ to a member of $R$. This is exactly the form in which the lemma is used to prove that the male-propose deferred-acceptance mechanism is strategy-proof for the men: a single man's misreport can only create blocking pairs involving himself, while the lemma produces a blocking pair involving somebody else.
--
--   The standard proof splits on whether $\nu(R) = \mu(R)$. When the two sets of women differ, a woman in $\nu(R) \setminus \mu(R)$ together with her $\mu$-partner furnishes the pair directly, using only stability of $\mu$. When they coincide, the hybrid matching that follows $\nu$ on $R$ and $\mu$ elsewhere is a matching that all men of $R$ strictly prefer to $\mu$, and the conclusion is extracted from the deferred-acceptance run producing $\mu$.
-- source:
--   A. E. Roth, M. A. O. Sotomayor, Two-Sided Matching: A Study in Game-Theoretic Modeling and Analysis, Cambridge University Press 1990, Lemma 3.5 (the Blocking Lemma), pp. 47-48; originally D. Gale, M. Sotomayor, Ms. Machiavelli and the stable matching problem, American Mathematical Monthly 92 (1985), 261-268

import Definitions.Def_agt_matching

namespace AGT

/-- **The Blocking Lemma** (Gale–Sotomayor 1985; Roth–Sotomayor, *Two-Sided
Matching*, Lemma 3.5).  Let `mu` be a male-optimal stable matching for the strict
profiles `PM`, `PW`, let `nu` be an arbitrary matching, and let
`R = {m | PM m (nu m) (mu m)}` be the set of men who strictly prefer `nu` to `mu`.
If `R` is nonempty, witnessed by `m₀`, then `nu` is blocked by a pair `(m, nu m')`
with `m'` in `R` (so the blocking woman lies in `nu '' R`) and `m` outside `R`. -/
theorem blocking_lemma {M W : Type*} [Fintype M] [Fintype W]
    (PM : M → W → W → Prop) (PW : W → M → M → Prop)
    (hM : IsPrefProfile PM) (hW : IsPrefProfile PW)
    (mu nu : M ≃ W) (hmu : IsMaleOptimal PM PW mu)
    (m₀ : M) (hm₀ : PM m₀ (nu m₀) (mu m₀)) :
    ∃ m m' : M, PM m' (nu m') (mu m') ∧ ¬ PM m (nu m) (mu m) ∧
      IsBlockingPair PM PW nu m (nu m') := by
  sorry

end AGT
