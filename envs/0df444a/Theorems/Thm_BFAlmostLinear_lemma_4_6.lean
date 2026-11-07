-- Prove2me | Theorems.Thm_BFAlmostLinear_lemma_4_6
-- name    : BFAlmostLinear.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:41:55.215872+00:00
-- url     : https://prove2.me/theorems/d72d4f84-6065-446d-bc28-27027ff0750e
-- title:
--   Lemma 4.6 — weighted 1-hop forward/backward searches of total weight $\tilde O(\Lambda b)$ in $\tilde O(mb)$ time whp
-- statement:
--   There is a deterministic program and an exponent $a$ with the following properties.
--
--   1. On every weighted graph with frozen flags satisfying (I1) and vertex weights $\lambda\ge0$, the program halts, and when it halts it has output, for every negative vertex $r$, a real $\Delta_r$, the set $V^{\mathrm{in}}_r=\{x: d^0(x,r)<\Delta_r\}$ with the distances $d^0(x,r)$, and the set $V^{\mathrm{out}}_r=\{x: d^1(r,x)<-\Delta_r\}$ with the distances $d^1(r,x)$.
--   2. For every $d>0$ there is $K$ such that for every such graph on $n$ vertices and $m$ arcs, every $\lambda\ge0$ with $\Lambda=\sum_v\lambda(v)$, and every $b\ge1$: if $U$ contains each negative vertex independently with probability $1/b$, then with probability at least $1-n^{-d}$, for every valid potential $\phi$ with
--   $$d^0_\phi(s,r)+d^1_\phi(r,t)\ge0\quad\forall r\in U,\ \forall s,t\in V,$$
--   the program run on $G_\phi$ halts within $K(m+1)\,b\,(\log(n+2))^a$ steps and its sets satisfy
--   $$\sum_{r\in N}\Big(\sum_{v\in V^{\mathrm{in}}_r}\lambda(v)+\sum_{v\in V^{\mathrm{out}}_r}\lambda(v)\Big)\le K\,\Lambda\,b\,(\log(n+2))^a.$$
--
--   The balanced searches are the paper's weighted version of the [LLRZ26] searches.
--
--   **Formalization Note** The program does not receive $b$ or $U$: they appear only in the analysis. It reads $G_\phi$'s weights and the frozen flags.
--
--   Differences from the source:
--   - reading: "there is an algorithm … runs in $\tilde O(mb)$ time" → one deterministic program on the mission's machine (word bound $(m+n+2)^c$) that halts on every input and halts within $K(m+1)b(\log(n+2))^a$ steps on the good event; reason: the paper names no machine; $m+1$ keeps $m=0$ non-vacuous.
--   - encoding: $\tilde O(\Lambda b)$, "with high probability" → $K\Lambda b(\log(n+2))^a$ with probability $\ge1-n^{-d}$, $a$ absolute and $K$ after $d$; reason: footnotes 1–2, p.1.
--   - encoding: $\Delta_r$ → a finite real; reason: an infinite $\Delta_r$ of an exhausted search is replaced by a large finite value with the same sets.
--   - encoding: frozen flags → hypothesis `Frozen`; reason: §1.1, p.2; a valid $\phi$ keeps it for $G_\phi$.
-- source:
--   Hair, Li, Li, Zhang, Bellman-Ford in Almost-Linear Time, STOC 2027 submission (manuscript sha256 873b9acb…), Lemma 4.6, p.16

import Mathlib
import Definitions.Def_BFAlmostLinear_WGraph_I1
import Definitions.Def_BFAlmostLinear_flagInit

namespace BFAlmostLinear

/-- **Lemma 4.6**, p.16. "Consider a graph G that satisfies invariant (I1), with non-negative weight λ(v) on every vertex v.
Let Λ = Σ_{v∈V} λ(v) denote the total weight. There is an algorithm that, for every negative vertex r, computes ∆_r with
the following: • A set V^in_r = {x ∈ V : d⁰(x, r) < ∆_r} along with the distance d⁰(x, r) for every x in V^in_r. • A set
V^out_r = {x ∈ V : d¹(r, x) < −∆_r} along with the distance d¹(r, x) for every x in V^out_r. Moreover, … Let U ⊆ N be a random
sample where each vertex in N is sampled with probability 1/b. With high probability over the randomness of U, the
following holds. For any valid potential function ϕ such that d⁰_ϕ(s, r) + d¹_ϕ(r, t) ≥ 0 ∀r ∈ U, ∀s, t ∈ V, the algorithm on
the reweighted graph G_ϕ satisfies Σ_{r∈N} (Σ_{v∈V^in_r} λ(v) + Σ_{v∈V^out_r} λ(v)) ≤ Õ(Λb), and the algorithm runs in Õ(mb)
time."

Hair, Li, Li, Zhang, *Bellman-Ford in Almost-Linear Time*, STOC 2027 submission (manuscript sha256
873b9acb…), Lemma 4.6, p.16.

**Formalization Note.**
* One deterministic program. `b` is not an input: the sample only appears in the analysis. The word bound is `(m + n + 2)^c`.
* On every graph with (I1) whose unflagged arcs are nonnegative (`Frozen`), the program halts with `IsSearchOutput`. The run on `G_ϕ`
  reads `w_ϕ` and the frozen flags, not `(w, ϕ)`.
* `Õ` hides factors polylogarithmic in `n` (footnote 1, p.1): it is `(log(n + 2))^a`, with `a` absolute and `K` chosen
  after the probability exponent `d`. The time is `K (m + 1) b (log(n + 2))^a`; `m + 1` makes `m = 0` non-vacuous.
* `G` may carry auxiliary arcs (Lemma 4.6 is stated for a graph with (I1)); `d⁰`, `d¹` ignore them. The good event
  comes before `ϕ`. `Λ = 0` is included. -/
theorem lemma_4_6 :
    ∃ (P : Machine.Program) (a : ℕ), Machine.NoCoin P ∧
      (∀ (n m : ℕ) (G : WGraph (Fin n) (Fin m)) (lam : Fin n → ℝ),
        G.I1 → G.Frozen → (∀ v, 0 ≤ lam v) →
        let W := Machine.wordBound P (m + n + 2)
        let σ₀ := flagInit G 0 0 lam
        (∃ T, Machine.HaltsWithin P W Machine.zeroTape σ₀ T) ∧
        ∀ T, Machine.HaltsWithin P W Machine.zeroTape σ₀ T →
          IsSearchOutput G (Machine.run P W Machine.zeroTape σ₀ T)) ∧
      ∀ d : ℝ, 0 < d → ∃ K : ℝ, 0 < K ∧
        ∀ (n m : ℕ) (G : WGraph (Fin n) (Fin m)) (lam : Fin n → ℝ) (b : ℝ),
          G.I1 → G.Frozen → (∀ v, 0 ≤ lam v) → 1 ≤ b →
          1 - (n : ℝ) ^ (-d) ≤
            goodMass G.negVertices b fun U =>
              ∀ ϕ : Fin n → ℝ, G.IsValid ϕ →
                (∀ r ∈ U, ∀ s t, 0 ≤ (G.reweight ϕ).dH 0 s r + (G.reweight ϕ).dH 1 r t) →
                let W := Machine.wordBound P (m + n + 2)
                let σ₀ := flagInit (G.reweight ϕ) 0 0 lam
                let L := Real.log ((n : ℝ) + 2) ^ a
                let T := ⌈K * ((m : ℝ) + 1) * b * L⌉₊
                let σ := Machine.run P W Machine.zeroTape σ₀ T
                Machine.HaltsWithin P W Machine.zeroTape σ₀ T ∧
                ∑ r ∈ G.negVertices, (∑ v ∈ listed σ 0 r, lam v + ∑ v ∈ listed σ 1 r, lam v) ≤
                  K * (∑ v, lam v) * b * L := by sorry

end BFAlmostLinear
