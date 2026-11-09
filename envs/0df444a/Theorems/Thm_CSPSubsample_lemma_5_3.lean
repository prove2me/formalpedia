-- Prove2me | Theorems.Thm_CSPSubsample_lemma_5_3
-- name    : CSPSubsample.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:33:18.577641+00:00
-- url     : https://prove2.me/theorems/351f482e-1b80-432d-869f-33b6ae8008c1
-- title:
--   Lemma 5.3 — deterministic suboptimality bound for $D_{\mathcal S}(\tilde\sigma)$
-- statement:
--   Let $U\subseteq[n]$ and $\mathcal S=(S_t)_{t\in[T]}$ with $S_t\subseteq U_{-t}$. Let $\phi^{(0)}$ be an optimal balanced assignment on $U$ ($\mathrm{val}^{\mathrm{bal}}_U(\phi^{(0)})=\mathrm{OPT}^{\mathrm{bal}}(U)$), let $\phi^{(1)},\dots,\phi^{(T)}$ be the best-response sequence of eq. (7), and $\tilde\sigma=(\phi^{(t-1)}|_{S_t})_{t\in[T]}$. Then
--   $$
--   \mathrm{OPT}^{\mathrm{bal}}(U)-\mathrm{val}^{\mathrm{bal}}_U(D_{\mathcal S}(\tilde\sigma))\le\sum_{t\in[T]}2\frac{|U_{-t}|^{k-1}}{|U|^k}\sum_{i\in U_t}\max_{a\in[q]}\left|\frac{H_{i,U_{-t}}(a,\phi^{(t-1)}|_{U_{-t}})}{|U_{-t}|^{k-1}}-\frac{H_{i,S_t}(a,\phi^{(t-1)}|_{S_t})}{|S_t|^{k-1}}\right|.
--   $$
--   By construction $\phi^{(t)}$ depends only on $S_1,\dots,S_t$ and $U$ (through $\phi^{(0)}$). The paper states the lemma as the existence of such a seed and sequence; the statement here names them. The bound says the extender loses only through how well the small seed set $S_t$ stands in for $U_{-t}$.
--
--   Differences from the source:
--   - generalization: there exist a seed σ̃ and a sequence ϕ^{(t)}, depending only on {S_{t'}}_{t'∈[t]} and U, with the bound → for every maximizer ϕ^{(0)} of val^bal_U, the bound holds with ϕ^{(t)} the sequence (7) from ϕ^{(0)} and σ̃ = (ϕ^{(t−1)}|_{S_t})_t; reason: these are the proof's witnesses; ϕ^{(t)} depends only on U and S_1, …, S_t by construction, and a maximizer exists, so the existential follows
--   - generalization: blocks V_1, …, V_T of size approximately n/T → an arbitrary block map b : [n] → [T]; reason: the statement holds for every partition of [n] into T blocks; it specializes to the paper's blocks
--   - generalization: ties in arg max broken in an arbitrary but deterministic way, consistently in (6) and (7) → an arbitrary maximizer-choosing rule tb (which may depend on the variable i), the same rule in (6) and (7); reason: the paper's rule is one such rule
--   - encoding: the exponent k − 1 for a k-CSP (k ≥ 1) → k − 1 in ℕ, so at k = 0 it is 0; reason: at k = 0 every H vanishes (no balanced tuple contains i) and the value is constant, so both sides are 0 under either convention
--   - encoding: H_{i,U_{−t}}(a, ϕ^{(t−1)}|_{U_{−t}}), H_{i,S_t}(a, ϕ^{(t−1)}|_{S_t}) → H evaluated at the total assignment ϕ^{(t−1)}; reason: H_{i,V} reads its assignment argument only on V
--   - encoding: a seed σ̄ ∈ ⨉_{t∈[T]} [q]^{S_t} → σ : [T] → [n] → [q], of which only σ_t on S_t is read; reason: the extender reads σ_t only on S_t, so the two seed spaces give the same assignments
--   - encoding: ϕ^{(0)}, …, ϕ^{(T)} ∈ [q]^U → total assignments in [q]^n, the variables outside U keeping their value under ϕ^{(0)}; reason: the statement reads these assignments only on U (agreement on U, val^bal_U, H_{i,V} with V ⊆ U), and the recursion (7) reads ϕ^{(t−1)} only on S_t ⊆ U
-- source:
--   Bernasconi, Castiglioni, Celli, Farina, Malavolta, A Subsampling Theorem for Constraint Satisfaction Problems with Large Arity, arXiv:2608.00203 (PDF sha256 fd9ae01113266fee273c46c14c8a1a39f36a958dba3fc276cd74bf4c3daff445), Lemma 5.3, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_CSPSubsample_Instance
import Definitions.Def_CSPSubsample_valbal
import Definitions.Def_CSPSubsample_extender

set_option autoImplicit false

namespace CSPSubsample

/-- **Lemma 5.3** (arXiv:2608.00203 (PDF sha256 fd9ae011…), p.15 = PDF p.17). Given `U ⊆ [n]` and
`S = (S_t)_{t ∈ [T]}` with `S_t ⊆ U_{−t}`, there exist a seed `σ̃` and a sequence `ϕ^{(t)}`, where
`ϕ^{(t)}` depends only on `{S_{t'}}_{t' ∈ [t]}` and `U`, such that
`OPT^bal(U) − val^bal_U(D_S(σ̃)) ≤ ∑_{t ∈ [T]} (2|U_{−t}|^{k−1}/|U|^k) ∑_{i ∈ U_t} max_{a ∈ [q]}
|H_{i,U_{−t}}(a, ϕ^{(t−1)}|_{U_{−t}})/|U_{−t}|^{k−1} − H_{i,S_t}(a, ϕ^{(t−1)}|_{S_t})/|S_t|^{k−1}|`.

**Formalization Note** The witnesses are explicit: `ϕ^{(t)}` is the sequence (7) started at any
maximizer `ϕ0` of `val^bal_U` (`phiSeq`, so `ϕ^{(t)}` is a function of `U`, `ϕ0` and
`S_1, …, S_t` by construction), and `σ̃ = seedOf …` is `(ϕ^{(t−1)}|_{S_t})_t`; the bound holds
for every such `ϕ0` and every tie-breaking rule. Lean block `t` is paper block `t + 1`, so the
paper's `ϕ^{(t−1)}` is `phiSeq … t.val`. `H` reads its assignment argument only on its set, so
the restrictions `|_{U_{−t}}`, `|_{S_t}` are implicit. All normalizers are powers;
`max_{a ∈ [q]}` is `⨆` over `Fin q`. The exponent `k − 1` is a natural number; at `k = 0`
every `H` vanishes and the balanced value is constant, so both sides are `0`. -/
theorem lemma_5_3 {n k q T : ℕ} (I : Instance n k q) (b : Fin n → Fin T) (U : Finset (Fin n))
    (S : Fin T → Finset (Fin n)) (hS : ∀ t, S t ⊆ blockCompl b U t)
    (tb : Fin n → (Fin q → ℝ) → Fin q) (htb : IsArgmaxRule tb)
    (ϕ0 : Fin n → Fin q) (hϕ0 : valbal I b U ϕ0 = OPTbal I b U) :
    OPTbal I b U - valbal I b U (extender I b S tb (seedOf I b U S tb ϕ0)) ≤
      ∑ t : Fin T, 2 * ((blockCompl b U t).card : ℝ) ^ (k - 1) / (U.card : ℝ) ^ k *
        ∑ i ∈ blockPart b U t, ⨆ a : Fin q,
          |Hval I b i (blockCompl b U t) a (phiSeq I b U S tb ϕ0 t.val) /
              ((blockCompl b U t).card : ℝ) ^ (k - 1) -
            Hval I b i (S t) a (phiSeq I b U S tb ϕ0 t.val) / ((S t).card : ℝ) ^ (k - 1)| := by sorry

end CSPSubsample
