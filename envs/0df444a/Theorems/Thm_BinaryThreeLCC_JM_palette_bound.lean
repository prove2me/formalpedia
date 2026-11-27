-- Prove2me | Theorems.Thm_BinaryThreeLCC_JM_palette_bound
-- name    : BinaryThreeLCC.JM.palette_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T05:02:22.236439+00:00
-- url     : https://prove2.me/theorems/c2286424-04fd-5b6f-9a38-67867bae6635
-- title:
--   Local-variance palette bound for parity-labelled coloured multigraphs (Lemma 5.3 with Fact 3.2)
-- statement:
--   Let $V$, $E$ and $C$ be finite sets with $C$ nonempty, $k=|C|$. Each edge $e\in E$ has endpoints $p(e),q(e)\in V$ and a colour $c(e)\in C$. Assume a parity labelling: for every colour $i$ there is $\varphi_i:V\to\mathbb F_2$ with
--
--   $$\varphi_i(p(e))+\varphi_i(q(e))=[c(e)=i]\qquad\text{for all }e\in E,\ i\in C .$$
--
--   (This holds when vertex labels in an $\mathbb F_2$-vector space add up along every edge of colour $i$ to $v_i$ and the $v_i$ are linearly independent; it rules out unique-colour cycles.) Let $d_i(v)$ be the number of edge-ends of colour $i$ at $v$ and $d(v)=\sum_i d_i(v)$. If $E\neq\emptyset$ and
--
--   $$\mathcal V=\frac1{|V|}\sum_{v}\frac1k\sum_{i}\Bigl(d_i(v)-\frac{d(v)}k\Bigr)^2\ \le\ \Bigl(\frac{|E|}{k|V|}\Bigr)^2,$$
--
--   then $k\le 60\log_2|V|$.
--
--   This is Lemma 5.3 of the source, with the no-unique-colour-cycle hypothesis replaced by the parity labelling that produces it.
-- source:
--   Janzer–Manohar, Reed–Muller Codes are Optimal Binary Linear 3-Query LCCs, STOC 2027 submission #732, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/732.pdf, Lemma 5.3 and its proof §5.1 (printed pp. 14, 17–18) together with Fact 3.2 (printed p. 9)

import Mathlib

set_option autoImplicit false

namespace BinaryThreeLCC.JM

theorem palette_bound {V E C : Type} [Fintype V] [Fintype E] [Fintype C]
    [DecidableEq V] [DecidableEq C] [Nonempty C]
    (p q : E → V) (c : E → C) (φ : C → V → ZMod 2)
    (hφ : ∀ i e, φ i (p e) + φ i (q e) = if c e = i then 1 else 0)
    (hE : 0 < Fintype.card E)
    (hvar : ∑ v, ∑ i, ((((Finset.univ.filter (fun e => c e = i ∧ p e = v)).card +
        (Finset.univ.filter (fun e => c e = i ∧ q e = v)).card : ℕ) : ℝ) -
        (((Finset.univ.filter (fun e => p e = v)).card +
          (Finset.univ.filter (fun e => q e = v)).card : ℕ) : ℝ) / Fintype.card C) ^ 2 ≤
      (Fintype.card V : ℝ) * Fintype.card C *
        ((Fintype.card E : ℝ) / (Fintype.card C * Fintype.card V)) ^ 2) :
    (Fintype.card C : ℝ) ≤ 60 * Real.logb 2 (Fintype.card V) := by sorry

end BinaryThreeLCC.JM
