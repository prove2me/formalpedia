-- Prove2me | Theorems.Thm_CNFLearnMQ_lemma_5_22
-- name    : CNFLearnMQ.lemma_5_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:18:12.931841+00:00
-- url     : https://prove2.me/theorems/cc824bf9-5eb9-405b-b279-3b87344cd9fe
-- title:
--   Lemma 5.22 — $E_{\mathrm{core}}$ holds w.p. $\ge 1-\delta/6$ and controls $\widehat q_s(b)$
-- statement:
--   Let $t\ge1$ be real, $k\ge100$ and $d\ge1$ integers satisfying the local lemma condition (3), $k\ge(1+1/t)\log d+2\log k+t-3\log t+5$, and let $\Phi=(V,C)$ be an $n$-variable $(k,d)$-CNF formula with $n\ge k$ (the standing assumptions of §5, p.21, and §3, p.13).
--   Fix $\varepsilon,\delta\in(0,1)$. Then:
--
--   1. The event $E_{\mathrm{core}}$ on a pool of $N_{\mathrm{pool}}$ independent samples from $\mu_\Phi$ occurs with probability at least $1-\delta/6$.
--   2. On $E_{\mathrm{core}}$, consider any call to ExtendSubclause$(s,Y)$ with $s=(S,\sigma_S)$ and $q_s>0$. Every signed core $b=(B,\tau_B)$ recovered in this call with $B\cap S=\emptyset$ and $1\le|B|\le k-|S|$ satisfies
--   $$q_s(b)\ge\widehat q_s(b)-\phi.$$
--
--   Combined with Lemma 5.18 this supplies the hypothesis of Lemma 5.8 with high probability.
--
--   Differences from the source:
--   - generalization: a call to ExtendSubclause$(s,Y)$ (made when $\widehat q_s>2\eta$ and $|S|<k$) with families returned by LearnCore → every $s$ with $q_s>0$ and $\widehat q_s>2\eta$ on a pool of length $N_{\mathrm{pool}}$, and every recovered families $\widehat{\mathcal R}_{Z_i}\subseteq\mathcal R_{Z_i}$; reason: LearnCore always returns genuine cores (Theorem 4.5), and for $|S|=k$ no $b$ with $1\le|B|\le k-|S|$ exists
--   - encoding: $|B|\le k-|S|$ → $|B|+|S|\le k$; reason: equivalent over the naturals
--   - encoding: $\mu_\Phi$, defined when $\Omega(\Phi)\ne\emptyset$ (p.13); under (3) $\Phi$ is satisfiable by Theorem 3.1 → nonemptiness of the solution set is a hypothesis `h`; reason: the published law `solutionLaw` needs the proof; under the standing assumptions it always holds, so no instance is excluded
-- source:
--   Feng, Yu, Zhang, Learning CNF Formulas with Uniform Random Solutions and Membership Queries, STOC 2027 submission (manuscript sha256 519ee6d4…), Lemma 5.22, pp.35–36 (Definition 5.21 and eq. (13), p.35)

import Mathlib
import Definitions.Def_CNFLearnMQ_Success

set_option autoImplicit false

namespace CNFLearnMQ

open CNFLearning873.Valiant

/-- Lemma 5.22, pp.35–36 (Feng, Yu, Zhang, *Learning CNF Formulas with Uniform Random Solutions and Membership Queries*, STOC 2027 submission (manuscript sha256 519ee6d4…)). Under the standing assumptions of §5:
1. the event `E_core` (Definition 5.21, p.35) on the pool `Y` of `N_pool` independent samples from
   `µ_Φ` occurs with probability at least `1 − δ/6`;
2. on `E_core`, in any call to ExtendSubclause(s, Y) with `q_s > 0` (a call happens when
   `q̂_s > 2η`), every signed core `b = (B, τ_B)` recovered in the call with `B ∩ S = ∅` and
   `1 ≤ |B| ≤ k − |S|` satisfies `q_s(b) ≥ q̂_s(b) − ϕ`.

**Formalization Note** In item 2 the recovered families are any `R̂_{Zᵢ} ⊆ R_{Zᵢ}` (LearnCore always
returns genuine cores, Theorem 4.5), the selected samples are the first `N_ext` violating pool
samples, and `|B| ≤ k − |S|` is written `|B| + |S| ≤ k`. `µ_Φ` exists only when `Ω(Φ) ≠ ∅`, so
nonemptiness is a hypothesis (it always holds under (3), Theorem 3.1). -/
theorem lemma_5_22 {n k d : ℕ} {t ε δ : ℝ} (ht : 1 ≤ t) (hk : 100 ≤ k) (hd : 1 ≤ d) (hLLL : LLLCondition k d t) (hn : k ≤ n) (hε0 : 0 < ε) (hε1 : ε < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (Φ : CNF n) (hΦ : KD Φ k d) (h : (solutions Φ).Nonempty) :
    ENNReal.ofReal (1 - δ / 6) ≤
      prob (iidList (solutionPMF Φ h) (Npool n k d t ε δ))
        (ECore Φ h k (Next n k d δ) (phi d k)) ∧
    ∀ Y : List (Assignment n), Y.length = Npool n k d t ε δ →
      ECore Φ h k (Next n k d δ) (phi d k) Y →
      ∀ s : Clause n, 0 < q Φ h s → 2 * eta n k d t ε < qhatPool Y s →
      ∀ Rs : List (Finset (Finset (Fin n))),
        List.Forall₂ (fun Z R => R ⊆ cores Φ Z) (firstViolating Y s (Next n k d δ)) Rs →
        ∀ b ∈ candidateCores (firstViolating Y s (Next n k d δ)) Rs,
          Disjoint (support s) (support b) → 1 ≤ width b → width b + width s ≤ k →
          qhatCore (Next n k d δ) (firstViolating Y s (Next n k d δ)) Rs b - phi d k ≤
            qcond Φ h s b := by sorry

end CNFLearnMQ
