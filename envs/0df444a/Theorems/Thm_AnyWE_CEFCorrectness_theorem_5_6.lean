-- Prove2me | Theorems.Thm_AnyWE_CEFCorrectness_theorem_5_6
-- name    : AnyWE.CEFCorrectness.theorem_5_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:52:53.216505+00:00
-- url     : https://prove2.me/theorems/fe441583-3645-45e3-8c2c-5fdaf69ce7b6
-- title:
--   Theorem 5.6 — a PEF proof of indistinguishability and an endpoint EF proof give a $(t',s',\ell,\epsilon')$-PEF proof of correctness
-- statement:
--   Fix a bound $k\ge2$ on the premises of Logical Inference. There is a fixed polynomial $p$ such that the following holds. Fix integers $m,t,s,\ell,q\ge1$ and $0<\epsilon<1$. Let $\mathrm{Gen}^{(0)},\mathrm{Gen}^{(1)}$ be circuit samplers at a fixed $\lambda$ with common input length $n$ that admit an $(m,t,s,\ell,\epsilon)$-PEF proof of indistinguishability (Definition 5.3). Let $F$ be a deterministic circuit on $n$ input bits with the samplers' output length, and suppose there is an EF proof of length at most $q$ of
--   $$D_k(x;r)=F(x),\qquad(\mathrm{aux},D_k)\leftarrow\mathrm{Gen}^{(1)}(1^\lambda;\rho),$$
--   with $\rho,x,r$ proper variables. Put $\sigma=\max\{s,2^\ell\}$,
--   $$t'=p(t+q+n+|F|)\cdot\sigma^2,\qquad s'=p(t+q+n+|F|)\cdot\sigma,\qquad \frac1{\epsilon'}=\frac1\epsilon-p(t+n)\cdot\sigma,$$
--   and assume the right-hand side of the last equation is positive. Then the correctness assertion
--   $$C_k(x;r)=F(x),\qquad(\mathrm{aux},C_k)\leftarrow\mathrm{Gen}^{(0)}(1^\lambda;\rho),$$
--   represented by the gate equations of $\mathrm{Gen}^{(0)}$, of its sampled circuit and of $F$ with the equality of the two outputs, where $x$ are proper variables and $\rho,r$ independent random variables, admits a $(t',s',\ell,\epsilon')$-PEF proof.
--
--   This is the transfer principle of the paper: an indistinguishability argument plus an EF proof for the "ideal" endpoint gives a probabilistic proof for the "real" endpoint, with only polynomial loss when $\ell=O(\log\lambda)$.
--
--   Differences from the source:
--   - reading: "a constant number of formulas θ1, …, θc" in Logical Inference → at most k premises, for every k ≥ 2, with p chosen after k; reason: a constant fixed before the proof; k = 1 cannot combine two formulas, and for k ≥ 2 the systems agree up to polynomial factors.
--   - reading: Extension "e an extension variable" → e does not occur in Φ_{i−1} or in ψ; reason: §4.1.1 requires extension variables to be fresh, and Definition 4.26 says each extension variable is defined by an extension rule.
--   - encoding: a sampled circuit "with key k hardwired", whose full description the distinguisher receives → a fixed template with the key k as data; the distinguisher receives (aux, k), and an output step requires equal templates; reason: the paper's convention before Theorem 5.6 identifies a template with hardwired data with its universal-circuit evaluation; different templates give trivially distinguishable descriptions, and template changes go through EF equivalences.
--   - reading: "EF proofs establishing aux^(b) = aux′, C^(b)(x; r) = D^(b)(x; r)" → one EF proof per b of both equalities; reason: the two equalities are listed as one assertion per b.
--   - encoding: gate equations {out := C(in)} → one equation per gate plus one equation y_i ↔ (wire of output i) per output, hardwired bits as ⊤/⊥, the connectives = and ↔ identified, |C| = number of gates; reason: Lean representation of Definition 4.25; changes sizes by constant factors only.
--   - encoding: "Fix λ" → the samplers at λ are given directly as generator and template circuits, λ does not appear; reason: at a fixed λ only these circuits matter.
--   - encoding: the total encoding length of Definition 5.3 (samplers and generators as circuits with explicit wire lists, gadget decompositions, EF proofs) and the description length and running time of Gen′ in Definition 5.2 → the sum, over the generator and template of every sampler and every gadget circuit, of inputs + outputs + gates, plus the lengths of the supplied EF proofs; reason: polynomially related to a bit encoding of the same circuits, and the fixed polynomial p absorbs polynomial changes of t.
--   - encoding: "a fixed polynomial p" → p : Polynomial ℕ (natural coefficients); reason: the bounds are on natural-number lengths and every polynomial bound is dominated by one with natural coefficients.
-- source:
--   Jain, Jin, Mathialagan, SNARGs from any Witness Encryption, and More, STOC 2027 submission (manuscript sha256 9bc2f227…), p. 41, Theorem 5.6

import Mathlib
import Definitions.Def_AnyWE_CEFCorrectness_Sampler
set_option autoImplicit false

namespace AnyWE.CEFCorrectness

/-- **Theorem 5.6** (p. 41). For every premise bound `k ≥ 2` of Logical Inference there is a fixed
polynomial `p` such that: if `Gen^(0), Gen^(1)` (input length `n`) admit an `(m, t, s, ℓ, ϵ)`-PEF
proof of indistinguishability and the endpoint assertion `D_k(x; r) = F(x)` for `Gen^(1)` has an
EF proof of length at most `q` (with `ρ, x, r` proper variables), then the correctness assertion
`C_k(x; r) = F(x)` for `Gen^(0)` (with `x` proper and `ρ, r` random variables) admits a
`(t', s', ℓ, ϵ')`-PEF proof, where `σ = max{s, 2^ℓ}`, `t' = p(t + q + n + |F|)·σ²`,
`s' = p(t + q + n + |F|)·σ` and `1/ϵ' = 1/ϵ − p(t + n)·σ`, whenever the right-hand side is
positive. -/
theorem theorem_5_6 (k : ℕ) (hk : 2 ≤ k) :
    ∃ p : Polynomial ℕ, ∀ (m t s ℓ q : ℕ), 1 ≤ m → 1 ≤ t → 1 ≤ s → 1 ≤ ℓ → 1 ≤ q →
      ∀ ϵ : ℝ, 0 < ϵ → ϵ < 1 →
      ∀ (n a o : ℕ) (Gen₀ Gen₁ : SamplerAt n a o), PEFIndistAt k m t s ℓ ϵ Gen₀ Gen₁ →
      ∀ (F : Circuit n o) (efp : List (Finset Formula)),
        IsEFProof k (Gen₁.corrAssertion F .proper) efp → derivLength efp ≤ q →
        (0 : ℝ) < 1 / ϵ - ((p.eval (t + n) : ℕ) : ℝ) * ((max s (2 ^ ℓ) : ℕ) : ℝ) →
        ∃ cs : List (Finset Formula),
          IsPEFProof k (p.eval (t + q + n + F.size) * (max s (2 ^ ℓ)) ^ 2)
            (p.eval (t + q + n + F.size) * max s (2 ^ ℓ)) ℓ
            (1 / (1 / ϵ - ((p.eval (t + n) : ℕ) : ℝ) * ((max s (2 ^ ℓ) : ℕ) : ℝ)))
            (Gen₀.corrAssertion F .random) cs := by sorry

end AnyWE.CEFCorrectness
